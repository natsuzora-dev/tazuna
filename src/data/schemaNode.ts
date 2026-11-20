import { z } from "zod";

/**
 * The node form of a Zod schema, the one place that reads Zod's definitions. Any other type is opaque: `kind` is its
 * Zod type, `inner` the schema that it wraps, if any, and its children are the schemas that its definition holds.
 */
export type SchemaNode =
  | { readonly type: "array"; readonly element: z.ZodType }
  /** `catchall` is the schema of the fields that `shape` does not name, if any. */
  | {
      readonly type: "object";
      readonly shape: Readonly<Record<string, z.ZodType>>;
      readonly catchall: z.ZodType | undefined;
    }
  /** `discriminator` is the field that names the option of a z.discriminatedUnion; a plain z.union has none. */
  | { readonly type: "union"; readonly options: readonly z.ZodType[]; readonly discriminator: string | undefined }
  | { readonly type: "optional" | "nullable" | "default"; readonly inner: z.ZodType }
  /**
   * A codec: `in` is the side that messages carry and `out` the parsed side. `encode` and `decode` run only its encode
   * or decode transform, and give undefined when that fails.
   */
  | {
      readonly type: "codec";
      readonly in: z.ZodType;
      readonly out: z.ZodType;
      readonly encode: (value: unknown) => { readonly value: unknown } | undefined;
      readonly decode: (value: unknown) => { readonly value: unknown } | undefined;
    }
  | { readonly type: "pipe"; readonly in: z.ZodType; readonly out: z.ZodType }
  | { readonly type: "tuple"; readonly items: readonly z.ZodType[]; readonly rest: z.ZodType | undefined }
  | { readonly type: "record"; readonly key: z.ZodType; readonly value: z.ZodType }
  | { readonly type: "intersection"; readonly left: z.ZodType; readonly right: z.ZodType }
  | { readonly type: "lazy"; readonly inner: z.ZodType }
  | {
      readonly type: "opaque";
      readonly kind: string;
      readonly inner: z.ZodType | undefined;
      readonly children: readonly z.ZodType[];
    };

type Transform = (value: unknown, ctx: { readonly value: unknown; readonly issues: unknown[] }) => unknown;

const transformer =
  (transform: Transform) =>
  (value: unknown): { readonly value: unknown } | undefined => {
    try {
      const ctx = { value, issues: [] };
      const result = transform(value, ctx);
      return result instanceof Promise || ctx.issues.length > 0 ? undefined : { value: result };
    } catch {
      return undefined;
    }
  };

const schemaOrUndefined = (v: unknown): z.ZodType | undefined => (v instanceof z.ZodType ? v : undefined);

export function schemaNode(schema: z.ZodType): SchemaNode {
  const def = schema.def as unknown as Record<string, unknown> & { readonly type: string };
  const at = (key: string) => def[key] as z.ZodType;
  switch (def.type) {
    case "array":
      return { type: "array", element: at("element") };
    case "object": {
      const catchall = def["catchall"];
      return {
        type: "object",
        shape: def["shape"] as Record<string, z.ZodType>,
        catchall: catchall instanceof z.ZodType && !(catchall instanceof z.ZodNever) ? catchall : undefined,
      };
    }
    case "union":
      return {
        type: "union",
        options: def["options"] as z.ZodType[],
        discriminator: typeof def["discriminator"] === "string" ? def["discriminator"] : undefined,
      };
    case "optional":
    case "nullable":
    case "default":
      return { type: def.type, inner: at("innerType") };
    case "pipe": {
      const reverse = def["reverseTransform"];
      return typeof reverse === "function"
        ? {
            type: "codec",
            in: at("in"),
            out: at("out"),
            encode: transformer(reverse as Transform),
            decode: transformer(def["transform"] as Transform),
          }
        : { type: "pipe", in: at("in"), out: at("out") };
    }
    case "tuple":
      return { type: "tuple", items: def["items"] as z.ZodType[], rest: schemaOrUndefined(def["rest"]) };
    case "record":
      return { type: "record", key: at("keyType"), value: at("valueType") };
    case "intersection":
      return { type: "intersection", left: at("left"), right: at("right") };
    case "lazy":
      return { type: "lazy", inner: (def["getter"] as () => z.ZodType)() };
    default:
      return {
        type: "opaque",
        kind: def.type,
        inner: schemaOrUndefined(def["innerType"]),
        // A refinement in `checks` is a ZodCustom too, but a check, not a schema of the value.
        children: Object.entries(def)
          .flatMap(([key, v]) => (key === "checks" ? [] : v))
          .filter((v) => v instanceof z.ZodType),
      };
  }
}

export function childrenOf(node: SchemaNode): readonly z.ZodType[] {
  switch (node.type) {
    case "array":
      return [node.element];
    case "object":
      return [...Object.values(node.shape), ...(node.catchall === undefined ? [] : [node.catchall])];
    case "union":
      return node.options;
    case "codec":
    case "pipe":
      return [node.in, node.out];
    case "tuple":
      return [...node.items, ...(node.rest === undefined ? [] : [node.rest])];
    case "record":
      return [node.key, node.value];
    case "intersection":
      return [node.left, node.right];
    case "opaque":
      return node.children;
    default:
      return [node.inner];
  }
}

/** The schema of field `key` of an object node: its shape's, else the catchall, if any. */
export const fieldSchema = (node: Extract<SchemaNode, { type: "object" }>, key: string): z.ZodType | undefined =>
  Object.hasOwn(node.shape, key) ? node.shape[key] : node.catchall;

/** Whether a codec is at any depth of `schema`, `schema` included. */
export function holdsCodec(schema: z.ZodType, seen = new Set<z.ZodType>()): boolean {
  if (seen.has(schema)) return false;
  seen.add(schema);
  const node = schemaNode(schema);
  return node.type === "codec" || childrenOf(node).some((child) => holdsCodec(child, seen));
}

const tolerantSchemas = new WeakMap<z.ZodType, z.ZodType>();

export function tolerant(schema: z.ZodType): z.ZodType {
  const known = tolerantSchemas.get(schema);
  if (known !== undefined) return known;
  const node = schemaNode(schema);
  const rebuilt = (changes: Record<string, unknown>) => schema.clone({ ...schema.def, ...changes } as never);
  const result = ((): z.ZodType => {
    switch (node.type) {
      case "object": {
        const shape = Object.fromEntries(Object.entries(node.shape).map(([k, v]) => [k, tolerant(v)]));
        return rebuilt({ shape, catchall: node.catchall });
      }
      case "union":
        return rebuilt({ options: node.options.map(tolerant) });
      case "array":
        return rebuilt({ element: tolerant(node.element) });
      case "optional":
      case "nullable":
      case "default":
        return rebuilt({ innerType: tolerant(node.inner) });
      default:
        return schema;
    }
  })();
  tolerantSchemas.set(schema, result);
  return result;
}

const strictSchemas = new WeakMap<z.ZodType, z.ZodType>();
const openSchemas = new WeakMap<z.ZodType, z.ZodType>();

/**
 * Returns `schema` with every object at any depth rejecting a field that it does not name, as z.strictObject does; a
 * catchall stays. Each side of an intersection keeps every field, and the intersection rejects a field that neither
 * side names, since a check sees only the parsed value.
 */
export const strict = (schema: z.ZodType): z.ZodType => strictOf(schema, true);

function strictOf(schema: z.ZodType, closed: boolean): z.ZodType {
  const cache = closed ? strictSchemas : openSchemas;
  const known = cache.get(schema);
  if (known !== undefined) return known;
  const node = schemaNode(schema);
  const rebuilt = (changes: Record<string, unknown>) => schema.clone({ ...schema.def, ...changes } as never);
  const result = ((): z.ZodType => {
    switch (node.type) {
      case "object": {
        const shape = Object.fromEntries(Object.entries(node.shape).map(([k, v]) => [k, strict(v)]));
        const catchall = node.catchall === undefined ? (closed ? z.never() : z.unknown()) : strict(node.catchall);
        return rebuilt({ shape, catchall });
      }
      case "union":
        return rebuilt({ options: node.options.map((o) => strictOf(o, closed)) });
      case "array":
        return rebuilt({ element: strict(node.element) });
      case "optional":
      case "nullable":
      case "default":
        return rebuilt({ innerType: strictOf(node.inner, closed) });
      case "codec":
      case "pipe":
        return rebuilt({ in: strictOf(node.in, closed), out: strictOf(node.out, closed) });
      case "tuple":
        return rebuilt({ items: node.items.map(strict), rest: node.rest === undefined ? null : strict(node.rest) });
      case "record":
        return rebuilt({ valueType: strict(node.value) });
      case "intersection": {
        const both = rebuilt({ left: strictOf(node.left, false), right: strictOf(node.right, false) });
        const named = namedFields(node);
        return closed && named !== undefined ? both.check(unnamedFields(named)) : both;
      }
      case "lazy":
        return rebuilt({ getter: () => strictOf(node.inner, closed) });
      case "opaque":
        return node.inner === undefined ? schema : rebuilt({ innerType: strictOf(node.inner, closed) });
    }
  })();
  cache.set(schema, result);
  return result;
}

/** The fields that an object or an intersection of objects names, or undefined when it takes any field. */
function namedFields(node: SchemaNode): ReadonlySet<string> | undefined {
  if (node.type === "object") return node.catchall === undefined ? new Set(Object.keys(node.shape)) : undefined;
  if (node.type !== "intersection") return undefined;
  const [left, right] = [namedFields(schemaNode(node.left)), namedFields(schemaNode(node.right))];
  return left === undefined || right === undefined ? undefined : new Set([...left, ...right]);
}

const unnamedFields = (named: ReadonlySet<string>) =>
  z.check<unknown>((ctx) => {
    const value = ctx.value;
    if (value === null || typeof value !== "object" || Array.isArray(value)) return;
    const keys = Object.keys(value).filter((k) => !named.has(k));
    if (keys.length > 0) ctx.issues.push({ code: "unrecognized_keys", keys, input: value as Record<string, unknown> });
  });
