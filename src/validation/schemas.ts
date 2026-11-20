import type { Illegal } from "../data/illegal.generated.ts";
import { sameJson } from "../data/values.ts";
import type { Structure } from "../spec/structure.generated.ts";
import type { DefinitionStructure } from "../spec/structure.ts";

type Schema = { readonly [key: string]: unknown };

const field = (schema: unknown, key: string): unknown =>
  schema !== null && typeof schema === "object" && !Array.isArray(schema) && Object.hasOwn(schema, key)
    ? (schema as Schema)[key]
    : undefined;

/** Lean's unionOptions. */
function unionOptions(schema: unknown): readonly unknown[] | undefined {
  const anyOf = field(schema, "anyOf");
  if (Array.isArray(anyOf)) return anyOf;
  const oneOf = field(schema, "oneOf");
  return Array.isArray(oneOf) ? oneOf : undefined;
}

/** Lean's orderedKey. */
function orderedKey(item: unknown, key: string): boolean {
  const p = field(field(item, "properties"), key);
  if (p === undefined) return false;
  const [type, format] = [field(p, "type"), field(p, "format")];
  return (
    type === "number" || type === "integer" || (type === "string" && (format === "date-time" || format === "date"))
  );
}

const requiredOf = (option: unknown): string[] => {
  const required = field(option, "required");
  return Array.isArray(required) ? required.filter((k): k is string => typeof k === "string") : [];
};

const propertyConst = (option: unknown, k: string): unknown => field(field(field(option, "properties"), k), "const");

/** Lean's missesRequired. */
const missesRequired = (a: unknown, b: unknown): boolean =>
  field(a, "additionalProperties") === false &&
  requiredOf(b).some((k) => field(field(a, "properties"), k) === undefined);

const differ = (x: unknown, y: unknown): boolean => x !== undefined && y !== undefined && !sameJson(x, y);

/** Lean's apart. */
function apart(a: unknown, b: unknown): boolean {
  const [x, y] = [field(a, "type"), field(b, "type")];
  const numeric = new Set(["integer", "number"]);
  const types = typeof x === "string" && typeof y === "string" && x !== y && !(numeric.has(x) && numeric.has(y));
  return (
    types ||
    differ(field(a, "const"), field(b, "const")) ||
    [...requiredOf(a), ...requiredOf(b)].some((k) => differ(propertyConst(a, k), propertyConst(b, k))) ||
    missesRequired(a, b) ||
    missesRequired(b, a)
  );
}

const allApart = (options: readonly unknown[]): boolean =>
  options.every((o, i) => options.slice(i + 1).every((p) => apart(o, p)));

const propertiesOf = (schema: unknown): [string, unknown][] => {
  const properties = field(schema, "properties");
  return properties !== null && typeof properties === "object" && !Array.isArray(properties)
    ? Object.entries(properties)
    : [];
};

/** Lean's holdsCollection. */
function holdsCollection(schema: unknown): boolean {
  const additional = field(schema, "additionalProperties");
  const item = field(schema, "items");
  return (
    field(schema, "x-tazuna-sorted-by") !== undefined ||
    field(schema, "x-tazuna-bag") !== undefined ||
    field(schema, "x-tazuna-set") !== undefined ||
    (unionOptions(schema) ?? []).some(holdsCollection) ||
    (item !== undefined && holdsCollection(item)) ||
    propertiesOf(schema).some(([, p]) => holdsCollection(p)) ||
    (additional !== undefined && holdsCollection(additional))
  );
}

type Issue = { readonly path: readonly string[] } & (
  | { readonly kind: "unorderedSortKey"; readonly key: string }
  | { readonly kind: "ambiguousUnion" }
);

/** Lean's issues. */
function issues(path: readonly string[], schema: unknown): Issue[] {
  const key = field(schema, "x-tazuna-sorted-by");
  const item = field(schema, "items");
  const options = unionOptions(schema);
  const additional = field(schema, "additionalProperties");
  return [
    ...(typeof key === "string" && (item === undefined || !orderedKey(item, key))
      ? [{ path, kind: "unorderedSortKey", key } as const]
      : []),
    ...(options?.some(holdsCollection) && !allApart(options) ? [{ path, kind: "ambiguousUnion" } as const] : []),
    ...(options ?? []).flatMap((o) => issues(path, o)),
    ...(item === undefined ? [] : issues(path, item)),
    ...propertiesOf(schema).flatMap(([k, p]) => issues([...path, k], p)),
    ...(additional === undefined ? [] : issues(path, additional)),
  ];
}

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
          ...(st.map === null
            ? []
            : ([
                [[st.name, "key"], st.map.key],
                [[st.name, "context"], st.map.context],
              ] as [string[], unknown][])),
          ...(st.held === null ? [] : [[[st.name, "held"], st.held.schema] as [string[], unknown]]),
        ]),
      ];
  }
}

export function check(structure: Structure): Illegal[] {
  return structure.definitions.flatMap((d) =>
    schemasOf(d).flatMap(([path, schema]) =>
      issues(path, schema).map((issue): Illegal => {
        const definition = { service: d.service, name: d.name };
        return issue.kind === "unorderedSortKey"
          ? { kind: "Illegal.unorderedSortKey", definition, data: { path: [...issue.path], key: issue.key } }
          : { kind: "Illegal.ambiguousUnion", definition, data: { path: [...issue.path] } };
      }),
    ),
  );
}
