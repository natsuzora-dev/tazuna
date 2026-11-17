import type { Malformed } from "../data/malformed.ts";
import type { Definition, Named, Place, ServiceDefinition } from "../dsl/definition.ts";
import type { Found } from "./found.ts";

export interface DefinerExport {
  readonly definition: ServiceDefinition;
  readonly place: Place;
}

/**
 * Returns the service that owns the definition, or a Malformed violation. Returns null when the definition's definer,
 * or every definer that lists the entity, is exported but names a service that an earlier definer names;
 * duplicateService reports the cause.
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

/**
 * The services by name, each from the first export of its definer, and a duplicateService violation at the first export
 * of each later definer with a name that an earlier definer has.
 */
function servicesOf(definerExports: readonly DefinerExport[]): {
  readonly services: Map<string, { readonly definition: ServiceDefinition; readonly place: Place }>;
  readonly malformed: Found<Malformed>[];
} {
  const services = new Map<string, { readonly definition: ServiceDefinition; readonly place: Place }>();
  const malformed: Found<Malformed>[] = [];
  const seen = new Set<ServiceDefinition>();
  for (const { definition, place } of definerExports) {
    if (seen.has(definition)) continue;
    seen.add(definition);
    const earlier = services.get(definition.name);
    if (earlier === undefined) services.set(definition.name, { definition, place });
    else
      malformed.push({
        violation: {
          kind: "Malformed.duplicateService",
          definition: null,
          data: { name: definition.name, elsewhere: earlier.place.file },
        },
        place,
      });
  }
  return { services, malformed };
}

/** Assigns each definition the service that its definer names, or, for an entity, the definer that lists it. */
export function owners(
  found: readonly Omit<Named<Definition>, "service">[],
  definerExports: readonly DefinerExport[],
): {
  readonly services: ReadonlyMap<string, { readonly definition: ServiceDefinition; readonly place: Place }>;
  readonly definitions: Named<Definition>[];
  readonly malformed: Found<Malformed>[];
} {
  const { services, malformed: duplicates } = servicesOf(definerExports);
  const serviceNames = new Map([...services].map(([name, { definition }]) => [definition, name]));
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
    malformed: [...malformed, ...duplicates, ...listedUnderOtherName(services, definitions)],
  };
}
