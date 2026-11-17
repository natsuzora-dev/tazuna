import { z } from "zod";

/**
 * The node form of a Zod schema. Any other type is opaque, and its children are the schemas that its definition holds.
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
  | { readonly type: "opaque"; readonly children: readonly z.ZodType[] };

export function schemaNode(schema: z.ZodType): SchemaNode {
  const def = schema.def as unknown as Record<string, unknown> & { readonly type: string };
  switch (def.type) {
    case "array":
      return { type: "array", element: def["element"] as z.ZodType };
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
      return { type: def.type, inner: def["innerType"] as z.ZodType };
    case "lazy":
      return { type: "opaque", children: [(def["getter"] as () => z.ZodType)()] };
    default:
      // A refinement in `checks` is a ZodCustom too, but a check, not a schema of the value.
      return {
        type: "opaque",
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
    case "opaque":
      return node.children;
    default:
      return [node.inner];
  }
}

/** The schema of field `key` of an object node: its shape's, else the catchall, if any. */
export const fieldSchema = (node: Extract<SchemaNode, { type: "object" }>, key: string): z.ZodType | undefined =>
  Object.hasOwn(node.shape, key) ? node.shape[key] : node.catchall;
