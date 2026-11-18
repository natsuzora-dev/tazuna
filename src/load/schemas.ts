import { z } from "zod";
import { childrenOf, schemaNode } from "../data/schemaNode.ts";
import type { Shape } from "../data/values.ts";
import type { Definition } from "../dsl/definition.ts";
import { type AnyKeyedEntity, keyTarget } from "../dsl/entity.ts";
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
      if (node.type === "object") {
        for (const [key, v] of Object.entries(node.shape)) visit(v, [...path, key], inside);
        if (node.catchall !== undefined) visit(node.catchall, path, inside);
      }
      // A codec's output is the parsed side, which no message carries, so the walk takes only its input.
      else for (const child of node.type === "codec" ? [node.in] : childrenOf(node)) visit(child, path, inside);
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

/** Lean's KeyPosition: a field path to a value whose schema is `ref(entity)` or `entity`'s key field. */
export interface KeyPosition {
  readonly path: readonly string[];
  readonly entity: AnyKeyedEntity;
}

/**
 * Returns the key positions of `shape`, each path once: a key schema and the nullable or default around it are found on
 * the same path. Lines and records rename created keys at these positions.
 */
export function keyPositions(shape: Shape): KeyPosition[] {
  const found = new Map<string, KeyPosition>();
  for (const { path, schema } of schemasIn(shape, [])) {
    const entity = keyTarget(schema);
    const at = JSON.stringify(path);
    if (entity !== undefined && !found.has(at)) found.set(at, { path, entity });
  }
  return [...found.values()];
}
