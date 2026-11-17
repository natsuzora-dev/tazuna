import { z } from "zod";
import { childrenOf, schemaNode } from "../data/schemaNode.ts";
import type { Definition } from "../dsl/definition.ts";
import { definitionKinds } from "../spec/structure.ts";

export interface SchemaAt {
  readonly path: readonly string[];
  readonly schema: z.ZodType;
}

export const isPlainObject = (value: object) => Object.getPrototypeOf(value) === Object.prototype;

const stopKinds = new Set<unknown>([...definitionKinds, "service"]);

/**
 * Returns whether `value` is a definition or a service. The walk stops there, so that a schema is found under the
 * definition that declares it.
 */
export const isDefinitionOrService = (value: object) => stopKinds.has((value as { readonly kind?: unknown }).kind);

/**
 * Returns whether `key` is an entity event's payload, which is made of its entity's fields and found under the entity.
 */
const derived = (definition: Definition, key: string) =>
  key === "payload" && definition.kind === "event" && definition.change !== "none";

export function schemasIn(value: unknown, path: readonly string[]): SchemaAt[] {
  const seen = new Set<object>();
  const found: SchemaAt[] = [];
  const visit = (value: unknown, path: readonly string[]): void => {
    if (typeof value !== "object" || value === null || seen.has(value) || isDefinitionOrService(value)) return;
    seen.add(value);
    const fields = (shape: object) => {
      for (const [key, v] of Object.entries(shape)) {
        const at = [...path, key];
        if (v instanceof z.ZodType) found.push({ path: at, schema: v });
        visit(v, at);
      }
    };
    if (value instanceof z.ZodType) {
      found.push({ path, schema: value });
      const node = schemaNode(value);
      if (node.type === "object") fields(node.shape);
      else for (const child of childrenOf(node)) visit(child, path);
    } else if (Array.isArray(value)) for (const v of value) visit(v, path);
    else if (isPlainObject(value)) fields(value);
  };
  visit(value, path);
  return found;
}

/** The entries of the definition that declare schemas. */
export const declaringEntries = (definition: Definition): [string, unknown][] =>
  Object.entries(definition).filter(([key]) => !derived(definition, key));

export const definitionSchemas = (definition: Definition): SchemaAt[] =>
  declaringEntries(definition).flatMap(([key, value]) => schemasIn(value, [key]));
