import { z } from "zod";
import { collectionOf } from "./collections.ts";
import { holdsCodec, schemaNode } from "./schemaNode.ts";
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

/** A Zod type that JSON cannot hold, or `union` for a plain union that holds a codec, whose option no tag names. */
export type UnrepresentableType = (typeof unrepresentableTypes)[number] | "union";

export function unrepresentableType(schema: z.ZodType): UnrepresentableType | undefined {
  const node = schemaNode(schema);
  if (node.type === "union")
    return node.discriminator === undefined && node.options.some((o) => holdsCodec(o)) ? "union" : undefined;
  return node.type === "opaque" ? unrepresentableTypes.find((type) => type === node.kind) : undefined;
}

export const jsonSchema = (schema: z.ZodType): JsonSchema =>
  z.toJSONSchema(schema, {
    io: "input",
    unrepresentable: "any",
    // `format` already states the date, date-time and duration forms; Zod's regex `pattern` would repeat it.
    override: (ctx) => {
      if (["date-time", "date", "duration"].includes(String(ctx.jsonSchema.format))) delete ctx.jsonSchema.pattern;
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
