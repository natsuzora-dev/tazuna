import type { Illegal } from "../data/illegal.generated.ts";
import { allApart, field, propertyOf, requiredOf, unionOptions } from "../data/unionOptions.ts";
import type { Structure } from "../spec/structure.generated.ts";
import { type DefinitionStructure, type StateStructure, schemaProperties } from "../spec/structure.ts";

/** Lean's orderedKey. */
function orderedKey(item: unknown, key: string): boolean {
  const p = propertyOf(item, key);
  if (p === undefined || !requiredOf(item).includes(key)) return false;
  if (field(p, "default") !== undefined) return false;
  const [type, format] = [field(p, "type"), field(p, "format")];
  return type === "number" || type === "integer" || (type === "string" && format === "date");
}

/** Lean's children. */
function children(schema: unknown): [string | undefined, unknown][] {
  const item = field(schema, "items");
  const additional = field(schema, "additionalProperties");
  return [
    ...(unionOptions(schema) ?? []).map((o): [undefined, unknown] => [undefined, o]),
    ...(item === undefined ? [] : [[undefined, item] as [undefined, unknown]]),
    ...schemaProperties(schema).map((k): [string, unknown] => [k, propertyOf(schema, k)]),
    ...(additional === undefined ? [] : [[undefined, additional] as [undefined, unknown]]),
  ];
}

/** Lean's holdsCollection. */
const holdsCollection = (schema: unknown): boolean =>
  field(schema, "x-tazuna-sorted-by") !== undefined ||
  field(schema, "x-tazuna-bag") !== undefined ||
  field(schema, "x-tazuna-set") !== undefined ||
  children(schema).some(([, c]) => holdsCollection(c));

type Issue = { readonly path: readonly string[] } & (
  | { readonly kind: "unorderedSortKey"; readonly key: string }
  | { readonly kind: "ambiguousUnion" }
);

/** Lean's issues. */
function issues(path: readonly string[], schema: unknown): Issue[] {
  const key = field(schema, "x-tazuna-sorted-by");
  const item = field(schema, "items");
  const options = unionOptions(schema);
  return [
    ...(typeof key === "string" && (item === undefined || !orderedKey(item, key))
      ? [{ path, kind: "unorderedSortKey", key } as const]
      : []),
    ...(options?.some(holdsCollection) && !allApart(options) ? [{ path, kind: "ambiguousUnion" } as const] : []),
    ...children(schema).flatMap(([k, c]) => issues(k === undefined ? path : [...path, k], c)),
  ];
}

/** Lean's mapKeyOf. */
const mapKeyOf = (st: StateStructure): [string[], unknown][] =>
  st.kind === "map" ? [[[st.name, "key"], st.map.key]] : [];

/** Lean's schemasOf. */
function schemasOf(d: DefinitionStructure): [string[], unknown][] {
  switch (d.kind) {
    case "entity":
      return [[["fields"], d.fields]];
    case "event":
      return [[["payload"], d.payload]];
    case "command":
    case "query":
      return [[["input"], d.input], ...(d.output === null ? [] : [[["output"], d.output] as [string[], unknown]])];
    case "automation":
      return [];
    case "machine":
    case "screen":
      return [
        [["context"], d.context],
        [["input"], d.input],
        [["output"], d.output],
        ...Object.entries(d.controls).flatMap(([k, p]): [string[], unknown][] =>
          p === null ? [] : [[["controls", k, "payload"], p]],
        ),
        ...d.states.flatMap((st): [string[], unknown][] => [
          ...mapKeyOf(st),
          ...(st.kind === "map" ? [[[st.name, "context"], st.map.context] as [string[], unknown]] : []),
          ...(st.held === null ? [] : [[[st.name, "held"], st.held.schema] as [string[], unknown]]),
        ]),
      ];
  }
}

/** Lean's defaultPaths. */
const defaultPaths = (path: readonly string[], schema: unknown): (readonly string[])[] => [
  ...(field(schema, "default") === undefined ? [] : [path]),
  ...children(schema).flatMap(([k, c]) => defaultPaths(k === undefined ? path : [...path, k], c)),
];

/** Lean's mapKeysOf. */
const mapKeysOf = (d: DefinitionStructure): [string[], unknown][] =>
  d.kind === "machine" || d.kind === "screen" ? d.states.flatMap(mapKeyOf) : [];

export function check(structure: Structure): Illegal[] {
  return structure.definitions.flatMap((d) => {
    const definition = { service: d.service, name: d.name };
    return [
      ...schemasOf(d).flatMap(([path, schema]) =>
        issues(path, schema).map(
          (issue): Illegal =>
            issue.kind === "unorderedSortKey"
              ? { kind: "Illegal.unorderedSortKey", definition, data: { path: [...issue.path], key: issue.key } }
              : { kind: "Illegal.ambiguousUnion", definition, data: { path: [...issue.path] } },
        ),
      ),
      ...mapKeysOf(d).flatMap(([at, schema]) =>
        defaultPaths(at, schema).map(
          (path): Illegal => ({ kind: "Illegal.defaultedMapKey", definition, data: { path: [...path] } }),
        ),
      ),
    ];
  });
}
