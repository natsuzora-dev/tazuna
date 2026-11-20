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

/** The JSON Schema of `schema` as parsing reads it, with every object closed by `strict`. */
export const jsonSchema = (schema: z.ZodType): JsonSchema =>
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
  }) as JsonSchema;

export function objectSchema(shape: Shape): JsonSchema {
  const { $schema: _, additionalProperties: __, ...schema } = jsonSchema(z.object(shape as Record<string, z.ZodType>));
  return schema;
}
