import type { Malformed } from "../data/malformed.ts";
import type { Definition, Named, Place, ServiceDefinition } from "../dsl/definition.ts";
import type { Found } from "./found.ts";

export interface DefinerExport {
  readonly folder: string;
  readonly definition: ServiceDefinition;
  readonly place: Place;
}

/**
 * Returns the service that owns the definition, or a Malformed violation. Returns null when the definition's definer,
 * or every definer that lists the entity, is exported but is no folder's service; serviceInSharedFolder reports the
 * cause.
 */
function owner(
  { name, definition }: Omit<Named<Definition>, "service">,
  serviceNames: ReadonlyMap<ServiceDefinition, string>,
  exported: ReadonlySet<ServiceDefinition>,
): { readonly service: string } | Malformed | null {
  if (definition.kind !== "entity") {
    const service = serviceNames.get(definition.service);
    if (service !== undefined) return { service };
    return exported.has(definition.service)
      ? null
      : { kind: "Malformed.missingDefiner", definition: null, data: { name } };
  }
  const lists = (d: ServiceDefinition) => Object.values(d.entities).includes(definition);
  const listing = [...serviceNames].filter(([d]) => lists(d)).map(([, service]) => service);
  if (listing.length === 1) return { service: listing[0] as string };
  if (listing.length > 1) return { kind: "Malformed.listedTwice", definition: null, data: { name, services: listing } };
  return [...exported].some(lists) ? null : { kind: "Malformed.unlistedEntity", definition: null, data: { name } };
}

function ambiguousServices(definerExports: readonly DefinerExport[]): Found<Malformed>[] {
  return definerExports.flatMap((e, i): Found<Malformed>[] => {
    const earlier = definerExports.slice(0, i);
    if (earlier.some((x) => x.folder === e.folder && x.definition === e.definition)) return [];
    if (earlier.some((x) => x.folder === e.folder && x.definition !== e.definition))
      return [
        {
          violation: { kind: "Malformed.serviceInSharedFolder", definition: null, data: { folder: e.folder } },
          place: e.place,
        },
      ];
    const elsewhere = earlier.find((x) => x.definition === e.definition && x.folder !== e.folder);
    if (elsewhere !== undefined)
      return [
        {
          violation: {
            kind: "Malformed.splitService",
            definition: null,
            data: { folder: e.folder, elsewhere: elsewhere.folder },
          },
          place: e.place,
        },
      ];
    return [];
  });
}

function listedUnderOtherName(
  services: ReadonlyMap<string, { readonly definition: ServiceDefinition; readonly place: Place }>,
  definitions: readonly Named<Definition>[],
): Found<Malformed>[] {
  const names = new Map(definitions.map((d) => [d.definition as unknown, d]));
  const definers = new Map([...services.values()].map((s) => [s.definition, s.place]));
  return [...definers].flatMap(([definer, place]) =>
    Object.entries(definer.entities).flatMap(([key, entity]): Found<Malformed>[] => {
      const named = names.get(entity);
      if (named === undefined || named.name === key) return [];
      const definition = { service: named.service, name: named.name };
      return [{ violation: { kind: "Malformed.listedUnderOtherName", definition, data: { key } }, place }];
    }),
  );
}

/** Reports each definer that is the service of no folder of its name, at the first folder whose service it is. */
function misnamedServices(
  services: ReadonlyMap<string, { readonly definition: ServiceDefinition; readonly place: Place }>,
): Found<Malformed>[] {
  const named = new Set(
    [...services].filter(([folder, s]) => folder === s.definition.name).map(([, s]) => s.definition),
  );
  const reported = new Set<ServiceDefinition>();
  return [...services].flatMap(([folder, { definition, place }]): Found<Malformed>[] => {
    if (named.has(definition) || reported.has(definition)) return [];
    reported.add(definition);
    return [
      {
        violation: { kind: "Malformed.misnamedService", definition: null, data: { folder, name: definition.name } },
        place,
      },
    ];
  });
}

/**
 * Assigns each definition its service. A folder's service is the first definer exported in it, and a definer's service
 * is the folder of its name when it is that folder's service, else the first folder whose service it is.
 */
export function owners(
  found: readonly Omit<Named<Definition>, "service">[],
  definerExports: readonly DefinerExport[],
): {
  readonly services: ReadonlyMap<string, { readonly definition: ServiceDefinition; readonly place: Place }>;
  readonly definitions: Named<Definition>[];
  readonly malformed: Found<Malformed>[];
} {
  const services = new Map<string, { readonly definition: ServiceDefinition; readonly place: Place }>();
  for (const { folder, definition, place } of definerExports)
    if (!services.has(folder)) services.set(folder, { definition, place });
  const serviceNames = new Map<ServiceDefinition, string>();
  for (const [folder, { definition }] of services)
    if (!serviceNames.has(definition) || folder === definition.name) serviceNames.set(definition, folder);
  const exported = new Set(definerExports.map((e) => e.definition));
  const definitions: Named<Definition>[] = [];
  const malformed: Found<Malformed>[] = [];
  for (const d of found) {
    const o = owner(d, serviceNames, exported);
    if (o === null) continue;
    if ("service" in o) definitions.push({ ...d, service: o.service });
    else malformed.push({ violation: o, place: d.place });
  }
  return {
    services,
    definitions,
    malformed: [
      ...malformed,
      ...listedUnderOtherName(services, definitions),
      ...ambiguousServices(definerExports),
      ...misnamedServices(services),
    ],
  };
}
