import { z } from "zod";
import { collectionOf } from "./collections.ts";
import type { Shape } from "./values.ts";

export type JsonSchema = Readonly<Record<string, unknown>>;

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
