import type { z } from "zod";
import { toJson, unionOption } from "./collections.ts";
import { collectionOf } from "./marks.ts";
import { fieldSchema, schemaNode, tolerant } from "./schemaNode.ts";
import type { Answer } from "./trace.generated.ts";
import { canonicalJson, objectOf, type Shape } from "./values.ts";

function canonical(shape: Shape, value: unknown): unknown {
  if (!value || typeof value !== "object" || Array.isArray(value)) return value;
  const fields = value as Record<string, unknown>;
  return Object.fromEntries(
    Object.entries(shape as Record<string, z.ZodType>).flatMap(([k, field]) => {
      const schema = tolerant(field);
      const given = Object.hasOwn(fields, k);
      const parsed = schema.safeParse(given ? fields[k] : undefined);
      if (!parsed.success) return given ? [[k, fields[k]]] : [];
      const encoded = toJson(schema, parsed.data);
      return encoded === undefined && !given ? [] : [[k, encoded]];
    }),
  );
}

export class Bag {
  readonly items: readonly unknown[];
  constructor(items: readonly unknown[]) {
    this.items = items;
  }
  toJSON(): readonly unknown[] {
    return this.items;
  }
}

export class Runs {
  readonly runs: readonly Bag[];
  constructor(runs: readonly Bag[]) {
    this.runs = runs;
  }
  toJSON(): readonly unknown[] {
    return this.runs.flatMap((r) => r.items);
  }
}

/** Lean's CValue.ref: a string whose schema is a key reference to `entity`. */
export class Ref {
  readonly entity: string;
  readonly value: string;
  constructor(entity: string, value: string) {
    this.entity = entity;
    this.value = value;
  }
  toJSON(): string {
    return this.value;
  }
}

/**
 * The key positions of a shape (Lean's KeyPosition): each field path, as JSON text, with the domain `<service>/<entity>`
 * of the keys there.
 */
export type KeyPositions = ReadonlyMap<string, string>;

function runsOf(items: readonly unknown[], key: string): Runs {
  const keyOf = (item: unknown) => JSON.stringify((item as Record<string, unknown> | null)?.[key]);
  const runs: unknown[][] = [];
  items.forEach((item, i) => {
    if (i > 0 && keyOf(item) === keyOf(items[i - 1])) runs.at(-1)?.push(item);
    else runs.push([item]);
  });
  return new Runs(runs.map((r) => new Bag(r)));
}

/** The value read by `schema` at field path `path`; array elements and union options do not extend the path. */
function bagged(schema: z.ZodType, value: unknown, keys: KeyPositions | undefined, path: readonly string[]): unknown {
  const entity = typeof value === "string" ? keys?.get(JSON.stringify(path)) : undefined;
  if (entity !== undefined) return new Ref(entity, value as string);
  const node = schemaNode(schema);
  switch (node.type) {
    case "array": {
      if (!Array.isArray(value)) return value;
      const items = value.map((v) => bagged(node.element, v, keys, path));
      const collection = collectionOf(schema);
      if (collection === undefined) return items;
      return collection.kind === "sortedBy" ? runsOf(items, collection.key) : new Bag(items);
    }
    case "object":
      if (!value || typeof value !== "object") return value;
      return Object.fromEntries(
        Object.entries(value).map(([k, v]) => {
          const field = fieldSchema(node, k);
          const at = Object.hasOwn(node.shape, k) ? [...path, k] : path;
          return [k, field === undefined ? v : bagged(field, v, keys, at)];
        }),
      );
    case "union": {
      const option = unionOption(node, value);
      return option === undefined ? value : bagged(option, value, keys, path);
    }
    case "optional":
    case "nullable":
    case "default":
      return value == null ? value : bagged(node.inner, value, keys, path);
    default:
      return value;
  }
}

const byText = (a: unknown, b: unknown) => {
  const [x, y] = [canonicalJson(a), canonicalJson(b)];
  return x < y ? -1 : x > y ? 1 : 0;
};

export function orderFree(value: unknown): unknown {
  if (value instanceof Ref) return value.value;
  if (value instanceof Bag) return value.items.map(orderFree).toSorted(byText);
  if (value instanceof Runs) return value.runs.flatMap((r) => orderFree(r) as unknown[]);
  if (Array.isArray(value)) return value.map(orderFree);
  if (value && typeof value === "object")
    return Object.fromEntries(Object.entries(value).map(([k, v]) => [k, orderFree(v)]));
  return value;
}

/** The value read by `shape`, with its bags, runs and, at the key positions `keys`, key references wrapped. */
export const comparable = (shape: Shape | undefined, value: unknown, keys?: KeyPositions): unknown =>
  shape === undefined ? value : bagged(objectOf(shape), canonical(shape, value), keys, []);

export const comparableAnswer = (answer: Answer, output: Shape | undefined, keys?: KeyPositions): Answer =>
  answer.result === "rejected"
    ? { result: answer.result, rejection: { kind: answer.rejection.kind } }
    : answer.output === undefined
      ? answer
      : { ...answer, output: comparable(output, answer.output, keys) };
