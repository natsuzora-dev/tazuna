import { z } from "zod";
import { date, datetime } from "./datetime.ts";
import { collectionOf } from "./marks.ts";
import { holdsCodec, schemaNode, strict } from "./schemaNode.ts";
import type { Json, Shape } from "./values.ts";

export type JsonSchema = { readonly [key: string]: Json };

/** The Zod types whose values JSON cannot hold, after Zod's toJSONSchema; a `transform` has no way back to JSON. */
export const unrepresentableTypes = [
  "bigint",
  "symbol",
  "undefined",
  "void",
  "nan",
  "date",
  "map",
  "set",
  "transform",
  "custom",
  "promise",
  "function",
  "file",
] as const;

/**
 * A Zod type that JSON cannot hold, `union` for a plain union that holds a codec, whose option no tag names, or
 * `intersection`, whose JSON Schema `allOf` cannot reject a field that neither side names.
 */
export type UnrepresentableType = (typeof unrepresentableTypes)[number] | "union" | "intersection";

export function unrepresentableType(schema: z.ZodType): UnrepresentableType | undefined {
  const node = schemaNode(schema);
  if (node.type === "intersection") return "intersection";
  if (node.type === "union")
    return node.discriminator === undefined && node.options.some((o) => holdsCodec(o)) ? "union" : undefined;
  return node.type === "opaque" ? unrepresentableTypes.find((type) => type === node.kind) : undefined;
}

const transformOf = (schema: z.core.$ZodType): unknown =>
  (schema._zod.def as { readonly transform?: unknown }).transform;

/** The decode transforms of tazuna's datetime and date, whose encoded order is their decoded order; a clone keeps it. */
const timeTransforms = new Set([datetime, date].map(transformOf));

const isSchema = (value: unknown): value is JsonSchema =>
  typeof value === "object" && value !== null && !Array.isArray(value);

/**
 * Returns `schema` with each union option that is a `$ref` replaced by the schema that it names, once: Zod writes a
 * recursive schema as a `$ref`, which states no type or field, so Lean's `fits` would take any value for the option.
 * The inlined schema keeps its own references, so a recursion is inlined only where a union names it.
 */
function inlineOptions(schema: JsonSchema): JsonSchema {
  const named = (ref: Json): Json | undefined => {
    if (ref === "#") return schema;
    const name = typeof ref === "string" && ref.startsWith("#/$defs/") ? ref.slice("#/$defs/".length) : undefined;
    const defs = schema["$defs"];
    return name !== undefined && isSchema(defs) ? defs[name] : undefined;
  };
  const option = (o: Json): Json => {
    if (!isSchema(o) || Object.keys(o).length !== 1 || o["$ref"] === undefined) return o;
    const target = named(o["$ref"]);
    if (!isSchema(target)) return o;
    const { $defs: _, $schema: __, ...inlined } = target;
    return inlined;
  };
  const walk = (value: Json): Json => {
    if (Array.isArray(value)) return value.map(walk);
    if (!isSchema(value)) return value;
    return Object.fromEntries(
      Object.entries(value).map(([key, v]) => [
        key,
        (key === "anyOf" || key === "oneOf") && Array.isArray(v)
          ? v.map((o) => {
              const inlined = option(o);
              return inlined === o ? walk(o) : inlined;
            })
          : walk(v),
      ]),
    );
  };
  return walk(schema) as JsonSchema;
}

/**
 * The JSON Schema of `schema` as parsing reads it, with every object closed by `strict` and each union option written
 * out (inlineOptions).
 */
export const jsonSchema = (schema: z.ZodType): JsonSchema =>
  inlineOptions(
    z.toJSONSchema(strict(schema), {
      io: "input",
      unrepresentable: "any",
      // `format` already states the date, date-time and duration forms; Zod's regex `pattern` would repeat it.
      override: (ctx) => {
        if (["date-time", "date", "duration"].includes(String(ctx.jsonSchema.format))) delete ctx.jsonSchema.pattern;
        // A codec other than tazuna's time codecs may decode to another order, which a sortedBy key cannot have.
        const node = schemaNode(ctx.zodSchema as unknown as z.ZodType);
        if (node.type === "codec" && !timeTransforms.has(transformOf(ctx.zodSchema)))
          ctx.jsonSchema["x-tazuna-codec"] = true;
        const collection = collectionOf(ctx.zodSchema);
        if (collection?.kind === "bag") ctx.jsonSchema["x-tazuna-bag"] = true;
        if (collection?.kind === "set") Object.assign(ctx.jsonSchema, { uniqueItems: true, "x-tazuna-set": true });
        if (collection?.kind === "sortedBy") ctx.jsonSchema["x-tazuna-sorted-by"] = collection.key;
      },
    }) as JsonSchema,
  );

export function objectSchema(shape: Shape): JsonSchema {
  const { $schema: _, additionalProperties: __, ...schema } = jsonSchema(z.object(shape as Record<string, z.ZodType>));
  return schema;
}
