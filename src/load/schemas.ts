import { z } from "zod";
import { childrenOf, schemaNode } from "../data/schemaNode.ts";
import type { Definition } from "../dsl/definition.ts";
import { definitionKinds } from "../spec/structure.ts";

export interface SchemaAt {
  readonly path: readonly string[];
  readonly schema: z.ZodType;
}

const isPlainObject = (value: object) => Object.getPrototypeOf(value) === Object.prototype;

const stopKinds = new Set<unknown>([...definitionKinds, "service"]);

/**
 * Returns whether `value` is a definition or a service. The walk stops there, so that a schema is found under the
 * definition that declares it.
 */
const isDefinitionOrService = (value: object) => stopKinds.has((value as { readonly kind?: unknown }).kind);

/**
 * Returns whether `key` is an entity event's payload, which is made of its entity's fields and found under the entity.
 */
const derived = (definition: Definition, key: string) =>
  key === "payload" && definition.kind === "event" && definition.change !== "none";

/** A codec's output is the parsed side, which no message carries, so the walk takes only its input. */
function childSchemas(schema: z.ZodType): readonly z.ZodType[] {
  const def = schema.def as { readonly type: string; readonly in?: z.ZodType };
  if (def.type === "pipe" && "reverseTransform" in def && def.in !== undefined) return [def.in];
  return childrenOf(schemaNode(schema));
}

/**
 * Returns each schema in `value` once per path to it, and not the schemas under one that `stop` holds for. A schema
 * that is its own descendant, through z.lazy, is walked once.
 */
export function schemasIn(value: unknown, path: readonly string[], stop?: (schema: z.ZodType) => boolean): SchemaAt[] {
  const seen = new Set<object>();
  const found: SchemaAt[] = [];
  const visit = (value: unknown, path: readonly string[], ancestors: ReadonlySet<z.ZodType>): void => {
    if (typeof value !== "object" || value === null || isDefinitionOrService(value)) return;
    if (value instanceof z.ZodType) {
      if (ancestors.has(value)) return;
      found.push({ path, schema: value });
      if (stop?.(value) === true) return;
      const inside = new Set(ancestors).add(value);
      const node = schemaNode(value);
      if (node.type === "object") for (const [key, v] of Object.entries(node.shape)) visit(v, [...path, key], inside);
      else for (const child of childSchemas(value)) visit(child, path, inside);
      return;
    }
    if (seen.has(value)) return;
    seen.add(value);
    if (Array.isArray(value)) for (const v of value) visit(v, path, ancestors);
    else if (isPlainObject(value)) for (const [key, v] of Object.entries(value)) visit(v, [...path, key], ancestors);
  };
  visit(value, path, new Set());
  return found;
}

export const definitionSchemas = (definition: Definition, stop?: (schema: z.ZodType) => boolean): SchemaAt[] =>
  Object.entries(definition)
    .filter(([key]) => !derived(definition, key))
    .flatMap(([key, value]) => schemasIn(value, [key], stop));
