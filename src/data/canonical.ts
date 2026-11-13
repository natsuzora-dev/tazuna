import { z } from "zod";
import { collectionOf } from "./collections.ts";
import { schemaNode } from "./schemaNode.ts";
import type { Answer, TraceLine } from "./trace.generated.ts";
import { contentOf, nameOf } from "./trace.ts";
import { canonicalJson, objectOf, type Shape } from "./values.ts";

export const alike = (a: TraceLine, b: TraceLine): boolean =>
  a.type === b.type && nameOf(a) === nameOf(b) && canonicalJson(contentOf(a)) === canonicalJson(contentOf(b));

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
        const catchall = (schema.def as { catchall?: unknown }).catchall;
        return rebuilt({ shape, catchall: catchall instanceof z.ZodNever ? undefined : catchall });
      }
      case "union":
        return rebuilt({ options: node.options.map(tolerant) });
      case "array":
        return rebuilt({ element: tolerant(node.element) });
      case "opaque":
        return schema;
      default:
        return rebuilt({ innerType: tolerant(node.inner) });
    }
  })();
  tolerantSchemas.set(schema, result);
  return result;
}

export function canonical(shape: Shape, value: unknown, options: { readonly tolerant?: boolean } = {}): unknown {
  if (!value || typeof value !== "object" || Array.isArray(value)) return value;
  const fields = value as Record<string, unknown>;
  return Object.fromEntries(
    Object.entries(shape as Record<string, z.ZodType>).flatMap(([k, field]) => {
      const schema = options.tolerant === true ? tolerant(field) : field;
      const parsed = schema.safeParse(fields[k]);
      if (!parsed.success) return k in fields ? [[k, fields[k]]] : [];
      const encoded = z.encode(schema, parsed.data as never);
      return encoded === undefined && !(k in fields) ? [] : [[k, encoded]];
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

function runsOf(items: readonly unknown[], key: string): Runs {
  const keyOf = (item: unknown) => JSON.stringify((item as Record<string, unknown> | null)?.[key]);
  const runs: unknown[][] = [];
  items.forEach((item, i) => {
    if (i > 0 && keyOf(item) === keyOf(items[i - 1])) runs.at(-1)?.push(item);
    else runs.push([item]);
  });
  return new Runs(runs.map((r) => new Bag(r)));
}

function bagged(schema: z.ZodType, value: unknown): unknown {
  const node = schemaNode(schema);
  switch (node.type) {
    case "array": {
      if (!Array.isArray(value)) return value;
      const items = value.map((v) => bagged(node.element, v));
      const collection = collectionOf(schema);
      if (collection === undefined) return items;
      return collection.kind === "sortedBy" ? runsOf(items, collection.key) : new Bag(items);
    }
    case "object":
      if (!value || typeof value !== "object") return value;
      return Object.fromEntries(
        Object.entries(value).map(([k, v]) => [k, node.shape[k] === undefined ? v : bagged(node.shape[k], v)]),
      );
    case "union": {
      const option = node.options.find((o) => tolerant(o).safeParse(value).success);
      return option === undefined ? value : bagged(option, value);
    }
    case "opaque":
      return value;
    default:
      return value == null ? value : bagged(node.inner, value);
  }
}

const byText = (a: unknown, b: unknown) => {
  const [x, y] = [canonicalJson(a), canonicalJson(b)];
  return x < y ? -1 : x > y ? 1 : 0;
};

export function orderFree(value: unknown): unknown {
  if (value instanceof Bag) return value.items.map(orderFree).toSorted(byText);
  if (value instanceof Runs) return value.runs.flatMap((r) => orderFree(r) as unknown[]);
  if (Array.isArray(value)) return value.map(orderFree);
  if (value && typeof value === "object")
    return Object.fromEntries(Object.entries(value).map(([k, v]) => [k, orderFree(v)]));
  return value;
}

export const comparable = (shape: Shape | undefined, value: unknown): unknown =>
  shape === undefined ? value : bagged(objectOf(shape), canonical(shape, value, { tolerant: true }));

export const comparableAnswer = (answer: Answer, output: Shape | undefined): Answer =>
  answer.result === "rejected"
    ? { result: answer.result, rejection: { kind: answer.rejection.kind } }
    : answer.output === undefined
      ? answer
      : { ...answer, output: comparable(output, answer.output) };
