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
  | { readonly type: "union"; readonly options: readonly z.ZodType[] }
  | { readonly type: "optional" | "nullable" | "default"; readonly inner: z.ZodType }
  /**
   * A codec: `in` is the side that messages carry and `out` the parsed side. `encode` runs only its encode transform,
   * and gives undefined when that fails.
   */
  | {
      readonly type: "codec";
      readonly in: z.ZodType;
      readonly out: z.ZodType;
      readonly encode: (value: unknown) => { readonly value: unknown } | undefined;
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

type Reverse = (value: unknown, ctx: { readonly value: unknown; readonly issues: unknown[] }) => unknown;

const encoder =
  (reverse: Reverse) =>
  (value: unknown): { readonly value: unknown } | undefined => {
    try {
      const ctx = { value, issues: [] };
      const wire = reverse(value, ctx);
      return wire instanceof Promise || ctx.issues.length > 0 ? undefined : { value: wire };
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
      return { type: "union", options: def["options"] as z.ZodType[] };
    case "optional":
    case "nullable":
    case "default":
      return { type: def.type, inner: at("innerType") };
    case "pipe": {
      const reverse = def["reverseTransform"];
      return typeof reverse === "function"
        ? { type: "codec", in: at("in"), out: at("out"), encode: encoder(reverse as Reverse) }
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

/** The issue codes of Zod's checks, as opposed to the codes of a value of another type or shape. */
const checkCodes = new Set<string>(["too_small", "too_big", "invalid_format", "not_multiple_of", "custom"]);

const onlyChecks = (issues: readonly z.core.$ZodIssue[]): boolean =>
  issues.every((i) => checkCodes.has(i.code) || (i.code === "invalid_union" && i.errors.some(onlyChecks)));

/**
 * Returns the option of a union that a value takes, with the value as `candidate` makes it for the option: the first
 * option that the value passes, as in Zod, else the first whose type and shape it has whatever the checks say, so that a
 * value that fails a check is written as it would be outside a union.
 */
export function unionOption(
  options: readonly z.ZodType[],
  candidate: (option: z.ZodType) => unknown,
): { readonly option: z.ZodType; readonly value: unknown } | undefined {
  const tried = options.map((option) => {
    const value = candidate(option);
    return { option, value, result: z.safeEncode(option, value as never) };
  });
  const found =
    tried.find((t) => t.result.success) ?? tried.find((t) => !t.result.success && onlyChecks(t.result.error.issues));
  return found && { option: found.option, value: found.value };
}
