import { z } from "zod";

/**
 * The node form of a Zod schema. Any other type is opaque, and its children are the schemas that its definition holds.
 */
export type SchemaNode =
  | { readonly type: "array"; readonly element: z.ZodType }
  | { readonly type: "object"; readonly shape: Readonly<Record<string, z.ZodType>> }
  | { readonly type: "union"; readonly options: readonly z.ZodType[] }
  | { readonly type: "optional" | "nullable" | "default"; readonly inner: z.ZodType }
  | { readonly type: "opaque"; readonly children: readonly z.ZodType[] };

export function schemaNode(schema: z.ZodType): SchemaNode {
  const def = schema.def as unknown as Record<string, unknown> & { readonly type: string };
  switch (def.type) {
    case "array":
      return { type: "array", element: def["element"] as z.ZodType };
    case "object":
      return { type: "object", shape: def["shape"] as Record<string, z.ZodType> };
    case "union":
      return { type: "union", options: def["options"] as z.ZodType[] };
    case "optional":
    case "nullable":
    case "default":
      return { type: def.type, inner: def["innerType"] as z.ZodType };
    case "lazy":
      return { type: "opaque", children: [(def["getter"] as () => z.ZodType)()] };
    default:
      return {
        type: "opaque",
        children: Object.values(def)
          .flat()
          .filter((v) => v instanceof z.ZodType),
      };
  }
}

export function childrenOf(node: SchemaNode): readonly z.ZodType[] {
  switch (node.type) {
    case "array":
      return [node.element];
    case "object":
      return Object.values(node.shape);
    case "union":
      return node.options;
    case "opaque":
      return node.children;
    default:
      return [node.inner];
  }
}
