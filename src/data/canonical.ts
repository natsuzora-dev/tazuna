import type { z } from "zod";
import { collectionOf, toJson, unionOption } from "./collections.ts";
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

/** Names the entity that a key-reference schema refers to, or returns undefined for any other schema. */
export type RefEntity = (schema: z.ZodType) => string | undefined;

function runsOf(items: readonly unknown[], key: string): Runs {
  const keyOf = (item: unknown) => JSON.stringify((item as Record<string, unknown> | null)?.[key]);
  const runs: unknown[][] = [];
  items.forEach((item, i) => {
    if (i > 0 && keyOf(item) === keyOf(items[i - 1])) runs.at(-1)?.push(item);
    else runs.push([item]);
  });
  return new Runs(runs.map((r) => new Bag(r)));
}

function bagged(schema: z.ZodType, value: unknown, refEntity: RefEntity | undefined): unknown {
  const entity = typeof value === "string" ? refEntity?.(schema) : undefined;
  if (entity !== undefined) return new Ref(entity, value as string);
  const node = schemaNode(schema);
  switch (node.type) {
    case "array": {
      if (!Array.isArray(value)) return value;
      const items = value.map((v) => bagged(node.element, v, refEntity));
      const collection = collectionOf(schema);
      if (collection === undefined) return items;
      return collection.kind === "sortedBy" ? runsOf(items, collection.key) : new Bag(items);
    }
    case "object":
      if (!value || typeof value !== "object") return value;
      return Object.fromEntries(
        Object.entries(value).map(([k, v]) => {
          const field = fieldSchema(node, k);
          return [k, field === undefined ? v : bagged(field, v, refEntity)];
        }),
      );
    case "union": {
      const option = unionOption(node, value);
      return option === undefined ? value : bagged(option, value, refEntity);
    }
    case "optional":
    case "nullable":
    case "default":
      return value == null ? value : bagged(node.inner, value, refEntity);
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

/** The value read by `shape`, with its bags, runs and, when `refEntity` names entities, key references wrapped. */
export const comparable = (shape: Shape | undefined, value: unknown, refEntity?: RefEntity): unknown =>
  shape === undefined ? value : bagged(objectOf(shape), canonical(shape, value), refEntity);

export const comparableAnswer = (answer: Answer, output: Shape | undefined, refEntity?: RefEntity): Answer =>
  answer.result === "rejected"
    ? { result: answer.result, rejection: { kind: answer.rejection.kind } }
    : answer.output === undefined
      ? answer
      : { ...answer, output: comparable(output, answer.output, refEntity) };
