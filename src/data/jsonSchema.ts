import { z } from "zod";
import { date, datetime, duration } from "./datetime.ts";
import { InternalError } from "./internalError.ts";
import { collectionOf } from "./marks.ts";
import type { SchemaStep } from "./schema.generated.ts";
import {
  checksOf,
  fieldSchema,
  holdsCodec,
  recursesEagerly,
  type SchemaNode,
  schemaNode,
  strict,
} from "./schemaNode.ts";
import { type Json, plain, type Shape } from "./values.ts";

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
 * A Zod type that JSON cannot hold, `union` for a plain union that holds a codec, whose option no tag names,
 * `intersection`, whose JSON Schema `allOf` cannot reject a field that neither side names, or `getter` for an object
 * that recursesEagerly.
 */
export type UnrepresentableType = (typeof unrepresentableTypes)[number] | "union" | "intersection" | "getter";

export function unrepresentableType(schema: z.ZodType): UnrepresentableType | undefined {
  const node = schemaNode(schema);
  if (node.type === "intersection") return "intersection";
  if (node.type === "object" && recursesEagerly(schema)) return "getter";
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
 * Returns `schema` with each union option that is a `$ref` written out once: Zod writes a recursive schema as a `$ref`,
 * which states no type, so Lean's `fits` would take any value for it. Once is enough: only a union that sorts or holds
 * a collection reads its options, and a recursion holds no collection (Malformed.opaqueCollection), so such a union
 * sits outside every recursion.
 */
function inlineOptions(schema: JsonSchema): JsonSchema {
  const named = (ref: Json): Json | undefined => {
    if (ref === "#") return schema;
    const name = typeof ref === "string" && ref.startsWith("#/$defs/") ? ref.slice("#/$defs/".length) : undefined;
    const defs = schema["$defs"];
    return name !== undefined && isSchema(defs) ? defs[name] : undefined;
  };
  const option = (o: Json): Json => {
    if (!isSchema(o) || o["$ref"] === undefined) return o;
    const target = named(o["$ref"]);
    if (!isSchema(target)) return o;
    const { $defs: _, $schema: __, ...inlined } = target;
    const { $ref: ___, ...own } = o;
    return { ...inlined, ...own };
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

const timeKinds = new Map<unknown, string>([
  [transformOf(datetime), "instant"],
  [transformOf(date), "date"],
  [transformOf(duration), "duration"],
]);

/**
 * What Lean's parse reads of `schema` beyond its JSON Schema `written`, to validate as Zod does: the checks in Zod's
 * order, which JSON Schema keywords do not keep; a nullable, which JSON Schema writes as a union with null; the
 * discriminator of a discriminated union; the kind of a tazuna time codec, which decodes and encodes its text; and
 * `x-tazuna-opaque` where only Zod can say what it does: a message of the author's, or a default that JSON cannot hold.
 */
function validation(schema: z.ZodType, written: Readonly<Record<string, unknown>>): JsonSchema {
  const def = schema._zod.def as unknown as Readonly<Record<string, unknown>>;
  const node = schemaNode(schema);
  const checks = checksOf(schema);
  const time = node.type === "codec" ? timeKinds.get(transformOf(schema)) : undefined;
  // Zod leaves out the default of a schema that holds a codec, which its JSON Schema writes encoded.
  const encodedDefault =
    node.type === "default" && written["default"] === undefined
      ? z.safeEncode(node.inner, def["defaultValue"])
      : undefined;
  const opaque =
    def["error"] !== undefined || checks.some((c) => c["check"] === "opaque") || encodedDefault?.success === false;
  return {
    ...(encodedDefault?.success === true ? { default: plain(encodedDefault.data) } : {}),
    ...(checks.length === 0 ? {} : { "x-tazuna-checks": checks }),
    ...(node.type === "nullable" ? { "x-tazuna-nullable": true } : {}),
    ...(node.type === "union" && node.discriminator !== undefined
      ? { "x-tazuna-discriminator": node.discriminator }
      : {}),
    ...(time === undefined ? {} : { "x-tazuna-time": time }),
    ...(opaque ? { "x-tazuna-opaque": true } : {}),
  };
}

/**
 * The JSON Schema of `schema` as parsing reads it, with every object closed by `strict` and each union option written
 * out (inlineOptions).
 */
export const jsonSchema = (schema: z.ZodType): JsonSchema => jsonSchemaOf(schema, false);

/** The JSON Schema of `schema`, with what Lean's parse reads beyond it (validation) when `validated`. */
const jsonSchemaOf = (schema: z.ZodType, validated: boolean): JsonSchema =>
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
        if (validated) Object.assign(ctx.jsonSchema, validation(ctx.zodSchema as unknown as z.ZodType, ctx.jsonSchema));
      },
    }) as JsonSchema,
  );

/** `schema` and each schema inside it that jsonSchema writes in its place. */
export function writtenAs(schema: z.ZodType): z.ZodType[] {
  const node = schemaNode(schema);
  const inner =
    node.type === "optional" || node.type === "default" || node.type === "lazy"
      ? node.inner
      : node.type === "codec" || node.type === "pipe"
        ? node.in
        : node.type === "opaque"
          ? node.inner
          : undefined;
  return inner === undefined ? [schema] : [schema, ...writtenAs(inner)];
}

/** The node that jsonSchema writes for `schema`. */
const written = (schema: z.ZodType): SchemaNode => schemaNode(writtenAs(schema).at(-1) ?? schema);

/**
 * The part of `schema` at `path` in its jsonSchema: a nullable is written as a union of what it wraps and null. A path
 * that the JSON Schema has and `schema` lacks is an InternalError.
 */
export function partAt(schema: z.ZodType, path: readonly SchemaStep[]): z.ZodType {
  return path.reduce((at, step) => {
    const node = written(at);
    const part =
      step.kind === "field" && node.type === "object"
        ? fieldSchema(node, step.name)
        : step.kind === "items" && node.type === "array"
          ? node.element
          : step.kind === "option" && node.type === "union"
            ? node.options[step.index]
            : step.kind === "option" && node.type === "nullable"
              ? [node.inner, z.null()][step.index]
              : undefined;
    if (part === undefined) throw new InternalError(`no part at ${JSON.stringify(step)} of a ${node.type} schema`);
    return part;
  }, schema);
}

/** The JSON Schema of an object of `shape` that the structure holds, with what Lean's parse reads beyond it. */
export function objectSchema(shape: Shape): JsonSchema {
  const {
    $schema: _,
    additionalProperties: __,
    ...schema
  } = jsonSchemaOf(z.object(shape as Record<string, z.ZodType>), true);
  return schema;
}
