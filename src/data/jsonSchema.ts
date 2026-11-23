import { z } from "zod";
import { collectionOf } from "./marks.ts";
import { checksOf, constantMessage, recursesEagerly, schemaNode, strict } from "./schemaNode.ts";
import type { Json, Shape } from "./values.ts";

export type JsonSchema = { readonly [key: string]: Json };

/** The Zod types whose values JSON cannot hold, after Zod's toJSONSchema. */
export const unrepresentableTypes = [
  "bigint",
  "symbol",
  "undefined",
  "void",
  "nan",
  "date",
  "map",
  "set",
  "custom",
  "promise",
  "function",
  "file",
] as const;

/**
 * A Zod type that JSON cannot hold, `intersection`, whose JSON Schema `allOf` cannot reject a field that neither side
 * names, or `getter` for an object that recursesEagerly.
 */
export type UnrepresentableType = (typeof unrepresentableTypes)[number] | "intersection" | "getter";

export function unrepresentableType(schema: z.ZodType): UnrepresentableType | undefined {
  const node = schemaNode(schema);
  if (node.type === "intersection") return "intersection";
  if (node.type === "object" && recursesEagerly(schema)) return "getter";
  return node.type === "opaque" ? unrepresentableTypes.find((type) => type === node.kind) : undefined;
}

const isSchema = (value: unknown): value is JsonSchema =>
  typeof value === "object" && value !== null && !Array.isArray(value);

/**
 * Returns `schema` with each `$ref` written out, and without `$defs` once nothing names them: Zod writes a schema that
 * a registry names, or a recursion, as a `$ref`, which states no type, so Lean's parse and `fits` would know nothing of
 * it. A `$ref` inside the schema that it names stays, since a recursion has no end; check reports z.lazy
 * (Restricted.schema), so only an unchecked spec has one.
 */
function inlineRefs(schema: JsonSchema): JsonSchema {
  const defs = schema["$defs"];
  const named = (ref: Json): Json | undefined => {
    if (ref === "#") return schema;
    const name = typeof ref === "string" && ref.startsWith("#/$defs/") ? ref.slice("#/$defs/".length) : undefined;
    return name !== undefined && isSchema(defs) ? defs[name] : undefined;
  };
  let kept = false;
  const walk = (value: Json, inside: readonly Json[]): Json => {
    if (Array.isArray(value)) return value.map((v) => walk(v, inside));
    if (!isSchema(value)) return value;
    const ref = value["$ref"];
    const target = ref === undefined ? undefined : named(ref);
    if (isSchema(target) && !inside.includes(ref ?? null)) {
      const { $defs: _, $schema: __, ...inlined } = target;
      const { $ref: ___, ...own } = value;
      return walk({ ...inlined, ...own }, [...inside, ref ?? null]);
    }
    if (ref !== undefined) kept = true;
    return Object.fromEntries(
      Object.entries(value).flatMap(([key, v]) => (key === "$defs" ? [] : [[key, walk(v, inside)]])),
    );
  };
  const inlined = walk(schema, []) as JsonSchema;
  return kept && defs !== undefined ? { ...inlined, $defs: defs } : inlined;
}

/**
 * What Lean's parse reads of `schema` beyond its JSON Schema, to validate as Zod does: the checks in Zod's
 * order, which JSON Schema keywords do not keep; a nullable, which JSON Schema writes as a union with null; the
 * discriminator of a discriminated union; the author's message written as a string; and `x-tazuna-opaque` where only
 * Zod can say what it does: a message that is a function, a refinement, or an overwrite.
 */
function validation(schema: z.ZodType): JsonSchema {
  const def = schema._zod.def as unknown as Readonly<Record<string, unknown>>;
  const node = schemaNode(schema);
  const checks = checksOf(schema);
  const message = constantMessage(def["error"]);
  const opaque = (def["error"] !== undefined && message === undefined) || checks.some((c) => c["check"] === "opaque");
  return {
    ...(checks.length === 0 ? {} : { "x-tazuna-checks": checks }),
    ...(node.type === "nullable" ? { "x-tazuna-nullable": true } : {}),
    ...(node.type === "union" && node.discriminator !== undefined
      ? { "x-tazuna-discriminator": node.discriminator }
      : {}),
    ...(message === undefined ? {} : { "x-tazuna-message": message }),
    ...(opaque ? { "x-tazuna-opaque": true } : {}),
  };
}

/**
 * The JSON Schema of `schema` as parsing reads it, with every object closed by `strict` and each `$ref` written out
 * (inlineRefs).
 */
export const jsonSchema = (schema: z.ZodType): JsonSchema => jsonSchemaOf(schema, false);

/**
 * The JSON Schema of `schema`, with what Lean's parse reads beyond it (validation) when `validated`, and the entity of
 * each key reference that `keyName` names as `x-tazuna-key`.
 */
const jsonSchemaOf = (
  schema: z.ZodType,
  validated: boolean,
  keyName: (schema: z.ZodType) => string | undefined = () => undefined,
): JsonSchema =>
  inlineRefs(
    z.toJSONSchema(strict(schema), {
      io: "input",
      unrepresentable: "any",
      // `format` already states the date form; Zod's regex `pattern` would repeat it.
      override: (ctx) => {
        if (ctx.jsonSchema.format === "date") delete ctx.jsonSchema.pattern;
        const collection = collectionOf(ctx.zodSchema);
        if (collection?.kind === "bag") ctx.jsonSchema["x-tazuna-bag"] = true;
        if (collection?.kind === "set") Object.assign(ctx.jsonSchema, { uniqueItems: true, "x-tazuna-set": true });
        if (collection?.kind === "sortedBy") ctx.jsonSchema["x-tazuna-sorted-by"] = collection.key;
        if (validated) Object.assign(ctx.jsonSchema, validation(ctx.zodSchema as unknown as z.ZodType));
        const key = keyName(ctx.zodSchema as unknown as z.ZodType);
        if (key !== undefined) ctx.jsonSchema["x-tazuna-key"] = key;
      },
    }) as JsonSchema,
  );

/**
 * The JSON Schema of an object of `shape` that the structure holds, with what Lean's parse reads beyond it, and the
 * entity `<service>/<name>` that `keyName` gives each key reference, by which verify reads a key as a reference.
 */
export function objectSchema(shape: Shape, keyName?: (schema: z.ZodType) => string | undefined): JsonSchema {
  const {
    $schema: _,
    additionalProperties: __,
    ...schema
  } = jsonSchemaOf(z.object(shape as Record<string, z.ZodType>), true, keyName);
  return schema;
}
