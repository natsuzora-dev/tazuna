import { z } from "zod";
import { markOf } from "./marks.ts";

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

/**
 * The checks that Zod runs on a value of `schema` once its type matches, in its order, each as its definition's data: a
 * schema that is a check itself, such as z.int() or z.email(), runs first. A check's message written as a string is its
 * `message`; one that is a function, which only Zod renders, makes it `{ check: "opaque" }`, as a refinement or an
 * overwrite does. A set's check is `{ check: "set" }`;
 * those of a bag and a sortedBy array check nothing.
 */
export function checksOf(schema: z.ZodType): readonly Readonly<Record<string, CheckData>>[] {
  const own = schema._zod.traits.has("$ZodCheck") ? [schema as unknown as z.core.$ZodCheck] : [];
  return [...own, ...(schema._zod.def.checks ?? [])].flatMap((c): Readonly<Record<string, CheckData>>[] => {
    const mark = markOf(c as z.core.$ZodCheck<never>);
    if (mark !== undefined) return mark.kind === "set" ? [{ check: "set" }] : [];
    const def = c._zod.def as unknown as Readonly<Record<string, unknown>>;
    const message = constantMessage(def["error"]);
    if (
      (def["error"] !== undefined && message === undefined) ||
      def["check"] === "custom" ||
      def["check"] === "overwrite"
    )
      return [{ check: "opaque" }];
    return [
      {
        ...(Object.fromEntries(
          Object.entries(def).filter(
            ([key, v]) => !["when", "pattern", "type", "coerce", "checks"].includes(key) && isCheckData(v),
          ),
        ) as Record<string, CheckData>),
        ...(message === undefined ? {} : { message }),
      },
    ];
  });
}

/**
 * The message of an error parameter that is a plain string, which Zod keeps as a function of no parameters, or
 * undefined for a function that may read the issue.
 */
export function constantMessage(error: unknown): string | undefined {
  if (typeof error !== "function" || error.length !== 0) return undefined;
  const message: unknown = error();
  return typeof message === "string" ? message : undefined;
}

/** A parameter of a check, which JSON holds. */
export type CheckData = string | number | boolean | null | readonly CheckData[];

const isCheckData = (v: unknown): v is CheckData =>
  v === null || ["string", "number", "boolean"].includes(typeof v) || (Array.isArray(v) && v.every(isCheckData));

/** The schema of field `key` of an object node: its shape's, else the catchall, if any. */
export const fieldSchema = (node: Extract<SchemaNode, { type: "object" }>, key: string): z.ZodType | undefined =>
  Object.hasOwn(node.shape, key) ? node.shape[key] : node.catchall;

const strictSchemas = new WeakMap<z.ZodType, z.ZodType>();
const strictening = new Set<z.ZodType>();

/**
 * Whether `schema` is its own descendant without a z.lazy on the way, as an object that names itself in a getter is.
 * Load reports it (Malformed.unrepresentableSchema): a walk of its children never ends, while z.lazy defers it.
 */
export function recursesEagerly(schema: z.ZodType): boolean {
  const seen = new Set<z.ZodType>();
  const reaches = (s: z.ZodType): boolean => {
    const node = schemaNode(s);
    if (node.type === "lazy") return false;
    return childrenOf(node).some((child) => {
      if (child === schema) return true;
      if (seen.has(child)) return false;
      seen.add(child);
      return reaches(child);
    });
  };
  return reaches(schema);
}

/**
 * Returns `schema` with every object at any depth rejecting a field that it does not name, as z.strictObject does; a
 * catchall stays. Load reports an intersection (Malformed.unrepresentableSchema), whose sides each see every field, and a
 * schema that recursesEagerly, which this returns as it is where it recurs.
 */
export function strict(schema: z.ZodType): z.ZodType {
  const known = strictSchemas.get(schema);
  if (known !== undefined) return known;
  if (strictening.has(schema)) return schema;
  strictening.add(schema);
  try {
    const result = strictened(schema);
    strictSchemas.set(schema, result);
    return result;
  } finally {
    strictening.delete(schema);
  }
}

function strictened(schema: z.ZodType): z.ZodType {
  const node = schemaNode(schema);
  const rebuilt = (changes: Record<string, unknown>) => schema.clone({ ...schema.def, ...changes } as never);
  switch (node.type) {
    case "object": {
      const shape = Object.fromEntries(Object.entries(node.shape).map(([k, v]) => [k, strict(v)]));
      return rebuilt({ shape, catchall: node.catchall === undefined ? z.never() : strict(node.catchall) });
    }
    case "union":
      return rebuilt({ options: node.options.map(strict) });
    case "array":
      return rebuilt({ element: strict(node.element) });
    case "optional":
    case "nullable":
    case "default":
      return rebuilt({ innerType: strict(node.inner) });
    case "codec":
    case "pipe":
      return rebuilt({ in: strict(node.in), out: strict(node.out) });
    case "tuple":
      return rebuilt({ items: node.items.map(strict), rest: node.rest === undefined ? null : strict(node.rest) });
    case "record":
      return rebuilt({ valueType: strict(node.value) });
    case "intersection":
      return rebuilt({ left: strict(node.left), right: strict(node.right) });
    case "lazy":
      return rebuilt({ getter: () => strict(node.inner) });
    case "opaque":
      return node.inner === undefined ? schema : rebuilt({ innerType: strict(node.inner) });
  }
}
