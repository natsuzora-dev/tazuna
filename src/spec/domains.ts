import type { Schema, SchemaStep } from "../data/schema.generated.ts";
import { canonicalJson, type Json, sameJson } from "../data/values.ts";
import type { Domain, Explore, Structure } from "./structure.generated.ts";
import { type DefinitionStructure, receivesOf, requestsOf, schemaIn } from "./structure.ts";

/** Lean's Tree: the values of a schema, as explore reads its JSON Schema with the declared domains. */
export type Tree =
  | { readonly kind: "listed"; readonly values: readonly Json[] }
  | { readonly kind: "union"; readonly options: readonly Tree[] }
  | { readonly kind: "object"; readonly fields: readonly Field[] }
  | { readonly kind: "undeclared"; readonly path: readonly SchemaStep[] };

interface Field {
  readonly name: string;
  readonly required: boolean;
  readonly tree: Tree;
}

/** Lean's Tree.values. */
export function treeValues(t: Tree): Json[] {
  switch (t.kind) {
    case "listed":
      return [...t.values];
    case "union":
      return t.options.flatMap(treeValues);
    case "object":
      return fieldsValues(t.fields).map((entries) => Object.fromEntries(entries));
    case "undeclared":
      return [];
  }
}

/** Lean's Fields.values. */
function fieldsValues(fields: readonly Field[]): (readonly [string, Json])[][] {
  const [first, ...rest] = fields;
  if (first === undefined) return [[]];
  const others = fieldsValues(rest);
  return [
    ...treeValues(first.tree).flatMap((v) => others.map((o) => [[first.name, v] as const, ...o])),
    ...(first.required ? [] : others),
  ];
}

/** Lean's Tree.undeclaredPaths. */
export function undeclaredPaths(t: Tree): (readonly SchemaStep[])[] {
  switch (t.kind) {
    case "listed":
      return [];
    case "union":
      return t.options.flatMap(undeclaredPaths);
    case "object":
      return t.fields.flatMap((f) => undeclaredPaths(f.tree));
    case "undeclared":
      return [t.path];
  }
}

/** Lean's declared: the first domain of `schema` at each path. */
export function declared(
  domains: readonly Domain[],
  schema: Schema,
): (path: readonly SchemaStep[]) => readonly Json[] | undefined {
  const byPath = new Map(
    domains
      .filter((d) => sameJson(d.schema, schema))
      .toReversed()
      .map((d) => [canonicalJson(d.path), d.values] as const),
  );
  return (path) => byPath.get(canonicalJson(path));
}

type Schemaish = { readonly [key: string]: Json };

const isObject = (v: Json | undefined): v is Schemaish => typeof v === "object" && v !== null && !Array.isArray(v);

/** Lean's treeOf. */
export function treeOf(
  named: (path: readonly SchemaStep[]) => readonly Json[] | undefined,
  s: Json,
  path: readonly SchemaStep[],
): Tree {
  const listed = named(path);
  if (listed !== undefined) return { kind: "listed", values: listed };
  const field = (key: string) => (isObject(s) ? s[key] : undefined);
  const union = (options: readonly Json[]): Tree => ({
    kind: "union",
    options: options.map((o, index) => treeOf(named, o, [...path, { kind: "option", index }])),
  });
  const [anyOf, oneOf, constant, values, type] = ["anyOf", "oneOf", "const", "enum", "type"].map(field);
  if (anyOf !== undefined) return Array.isArray(anyOf) ? union(anyOf) : { kind: "undeclared", path };
  if (oneOf !== undefined) return Array.isArray(oneOf) ? union(oneOf) : { kind: "undeclared", path };
  if (constant !== undefined) return { kind: "listed", values: [constant] };
  if (Array.isArray(values)) return { kind: "listed", values };
  if (Array.isArray(type)) return union(type.map((t) => ({ ...(s as Schemaish), type: t })));
  if (type === "null") return { kind: "listed", values: [null] };
  if (type === "boolean") return { kind: "listed", values: [false, true] };
  if (type === "object") {
    const additional = field("additionalProperties");
    if (isObject(additional) || additional === true) return { kind: "undeclared", path };
    const properties = field("properties");
    if (!isObject(properties)) return { kind: "listed", values: [{}] };
    const required = field("required");
    return {
      kind: "object",
      fields: Object.entries(properties).map(([name, p]) => ({
        name,
        required: Array.isArray(required) && required.includes(name),
        tree: treeOf(named, p, [...path, { kind: "field", name }]),
      })),
    };
  }
  return { kind: "undeclared", path };
}

const ref = (d: DefinitionStructure) => ({ service: d.service, name: d.name });

/** Lean's moveSchemas. */
export function moveSchemas(structure: Structure, service: string): Schema[] {
  const own = structure.definitions.filter((d) => d.service === service);
  const offersAny = (c: Extract<DefinitionStructure, { kind: "screen" }>, control: string) =>
    [Object.entries(c.offers), ...c.states.map((st) => Object.entries(st.offers))]
      .flat()
      .some(([k, o]) => k === control && o === "any");
  return [
    ...own.flatMap((d): Schema[] =>
      d.kind === "command" || d.kind === "query" ? [{ kind: "input", definition: ref(d) }] : [],
    ),
    ...requestsOf(structure, service).flatMap((r): Schema[] => {
      if (r.service === service) return [];
      const d = structure.definitions.find((x) => x.service === r.service && x.name === r.name);
      return (d?.kind === "command" || d?.kind === "query") && d.output !== null
        ? [{ kind: "output", definition: r }]
        : [];
    }),
    ...receivesOf(structure, service).map((event): Schema => ({ kind: "payload", event })),
    ...own.flatMap((d): Schema[] =>
      d.kind === "screen"
        ? Object.entries(d.controls).flatMap(([control, payload]): Schema[] =>
            payload !== null && offersAny(d, control) ? [{ kind: "control", screen: ref(d), control }] : [],
          )
        : [],
    ),
  ];
}

/** Lean's schemaTree?. */
export function schemaTree(structure: Structure, explore: Explore, schema: Schema): Tree | undefined {
  const json = schemaIn(structure, schema);
  return json === undefined ? undefined : treeOf(declared(explore.domains, schema), json, []);
}
