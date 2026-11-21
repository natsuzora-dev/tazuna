import { expectFound } from "../data/internalError.ts";
import type { Schema, SchemaStep } from "../data/schema.generated.ts";
import { isObject, type Json, sameJson } from "../data/values.ts";
import type { Structure } from "./structure.generated.ts";
import { type DefinitionStructure, type DomainStructure, receivesOf, requestsOf } from "./structure.ts";

/** Lean's Tree. */
export type Tree =
  | { readonly kind: "listed"; readonly values: readonly Json[] }
  | { readonly kind: "union"; readonly options: readonly Tree[] }
  | { readonly kind: "object"; readonly fields: readonly Field[] };

interface Field {
  readonly name: string;
  readonly required: boolean;
  readonly tree: Tree;
}

/** Lean's Undeclared. */
export type Undeclared = readonly (readonly SchemaStep[])[];

/** Lean's Except Undeclared Tree. */
export type TreeOf =
  | { readonly ok: true; readonly tree: Tree }
  | { readonly ok: false; readonly undeclared: Undeclared };

/** Lean's Tree.values. */
export function treeValues(t: Tree): Json[] {
  switch (t.kind) {
    case "listed":
      return [...t.values];
    case "union":
      return t.options.flatMap(treeValues);
    case "object":
      return fieldsValues(t.fields).map((entries) => Object.fromEntries(entries));
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

/** Lean's Node. */
type Node =
  | { readonly kind: "ref"; readonly name: string }
  | { readonly kind: "union"; readonly options: readonly Json[] }
  | { readonly kind: "types"; readonly types: readonly Json[] }
  | { readonly kind: "finite"; readonly values: readonly Json[] }
  | {
      readonly kind: "object";
      readonly properties: readonly (readonly [string, Json])[];
      readonly required: readonly Json[];
    }
  | { readonly kind: "undeclared" };

const undeclaredNode: Node = { kind: "undeclared" };

/** Lean's typed. */
function typed(s: Json, t: Json): Node {
  const field = (key: string) => (isObject(s) ? s[key] : undefined);
  if (t === "null") return { kind: "finite", values: [null] };
  if (t === "boolean") return { kind: "finite", values: [false, true] };
  if (t !== "object") return undeclaredNode;
  const additional = field("additionalProperties");
  if (isObject(additional) || additional === true) return undeclaredNode;
  const properties = field("properties");
  if (!isObject(properties)) return { kind: "finite", values: [{}] };
  const required = field("required");
  return { kind: "object", properties: Object.entries(properties), required: Array.isArray(required) ? required : [] };
}

const defsPrefix = "#/$defs/";

/** Lean's nodeOf. */
function nodeOf(s: Json): Node {
  const field = (key: string) => (isObject(s) ? s[key] : undefined);
  const [ref, anyOf, oneOf, constant, values, type] = ["$ref", "anyOf", "oneOf", "const", "enum", "type"].map(field);
  if (ref !== undefined)
    return typeof ref === "string" && ref.startsWith(defsPrefix)
      ? { kind: "ref", name: ref.slice(defsPrefix.length) }
      : undeclaredNode;
  if (anyOf !== undefined) return Array.isArray(anyOf) ? { kind: "union", options: anyOf } : undeclaredNode;
  if (oneOf !== undefined) return Array.isArray(oneOf) ? { kind: "union", options: oneOf } : undeclaredNode;
  if (constant !== undefined) return { kind: "finite", values: [constant] };
  if (Array.isArray(values)) return { kind: "finite", values };
  if (Array.isArray(type)) return { kind: "types", types: type };
  return type === undefined ? undeclaredNode : typed(s, type);
}

/** Lean's defsOf. */
const defsOf = (root: Json): readonly (readonly [string, Json])[] => {
  const defs = isObject(root) ? root["$defs"] : undefined;
  return isObject(defs) ? Object.entries(defs) : [];
};

/** Lean's options and fields: the undeclared paths of `results`, in order, which are none exactly when all are trees. */
const undeclaredOf = (results: readonly TreeOf[]): Undeclared => results.flatMap((r) => (r.ok ? [] : r.undeclared));

const treesOf = (results: readonly TreeOf[]): Tree[] => results.flatMap((r) => (r.ok ? [r.tree] : []));

type Declared = (path: readonly SchemaStep[]) => readonly Json[] | undefined;

/** Lean's treeOf. */
function treeOf(
  declared: Declared,
  defs: readonly (readonly [string, Json])[],
  s: Json,
  path: readonly SchemaStep[],
): TreeOf {
  const listed = declared(path);
  if (listed !== undefined) return { ok: true, tree: { kind: "listed", values: listed } };
  const object = (n: Extract<Node, { kind: "object" }>, at: readonly SchemaStep[]): TreeOf => {
    const results = n.properties.map(([name, p]) => treeOf(declared, defs, p, [...at, { kind: "field", name }]));
    const undeclared = undeclaredOf(results);
    if (undeclared.length > 0) return { ok: false, undeclared };
    const fields = treesOf(results).map((tree, i): Field => {
      const [name] = expectFound(`property ${i}`, n.properties[i]);
      return { name, required: n.required.includes(name), tree };
    });
    return { ok: true, tree: { kind: "object", fields } };
  };
  const union = (results: readonly TreeOf[]): TreeOf => {
    const undeclared = undeclaredOf(results);
    return undeclared.length > 0
      ? { ok: false, undeclared }
      : { ok: true, tree: { kind: "union", options: treesOf(results) } };
  };
  const node = nodeOf(s);
  switch (node.kind) {
    case "ref": {
      const entry = defs.find(([k]) => k === node.name);
      return entry === undefined
        ? { ok: false, undeclared: [path] }
        : treeOf(
            declared,
            defs.filter(([k]) => k !== node.name),
            entry[1],
            path,
          );
    }
    case "union":
      return union(node.options.map((o, index) => treeOf(declared, defs, o, [...path, { kind: "option", index }])));
    case "types":
      return union(
        node.types.map((t, index): TreeOf => {
          const at: SchemaStep[] = [...path, { kind: "option", index }];
          const values = declared(at);
          if (values !== undefined) return { ok: true, tree: { kind: "listed", values } };
          const n = typed(s, t);
          if (n.kind === "finite") return { ok: true, tree: { kind: "listed", values: n.values } };
          if (n.kind === "object") return object(n, at);
          return { ok: false, undeclared: [at] };
        }),
      );
    case "finite":
      return { ok: true, tree: { kind: "listed", values: node.values } };
    case "object":
      return object(node, path);
    case "undeclared":
      return { ok: false, undeclared: [path] };
  }
}

/** Lean's rootTree. */
export const rootTree = (declared: Declared, json: Json): TreeOf => treeOf(declared, defsOf(json), json, []);

/** Lean's domainOf. */
export const domainOf =
  (domains: readonly DomainStructure[], schema: Schema): Declared =>
  (path) =>
    domains.find((d) => sameJson(d.schema, schema) && sameJson(d.path, path))?.values;

const ref = (d: DefinitionStructure) => ({ service: d.service, name: d.name });

/** Lean's moveSchemas. */
export function moveSchemas(structure: Structure, service: string): [Schema, Json][] {
  const own = structure.definitions.filter((d) => d.service === service);
  const requested = requestsOf(structure, service);
  const received = receivesOf(structure, service);
  const named = (refs: readonly { service: string; name: string }[], d: DefinitionStructure) =>
    refs.some((r) => r.service === d.service && r.name === d.name);
  const offersAny = (c: Extract<DefinitionStructure, { kind: "screen" }>, control: string) =>
    [Object.entries(c.offers), ...c.states.map((st) => Object.entries(st.offers))]
      .flat()
      .some(([k, o]) => k === control && o === "any");
  return [
    ...own.flatMap((d): [Schema, Json][] =>
      d.kind === "command" || d.kind === "query" ? [[{ kind: "input", definition: ref(d) }, d.input]] : [],
    ),
    ...structure.definitions.flatMap((d): [Schema, Json][] =>
      d.service !== service && named(requested, d) && (d.kind === "command" || d.kind === "query") && d.output !== null
        ? [[{ kind: "output", definition: ref(d) }, d.output]]
        : [],
    ),
    ...structure.definitions.flatMap((d): [Schema, Json][] =>
      named(received, d) && d.kind === "event" ? [[{ kind: "payload", event: ref(d) }, d.payload]] : [],
    ),
    ...own.flatMap((d): [Schema, Json][] =>
      d.kind === "screen"
        ? Object.entries(d.controls).flatMap(([control, payload]): [Schema, Json][] =>
            payload !== null && offersAny(d, control) ? [[{ kind: "control", screen: ref(d), control }, payload]] : [],
          )
        : [],
    ),
  ];
}
