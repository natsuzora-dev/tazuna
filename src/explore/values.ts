import { expectFound } from "../data/internalError.ts";
import type { SchemaStep } from "../data/jsonSchema.ts";
import type { Scenario } from "../data/scenario.generated.ts";
import { canonicalJson, type Json, stringsOf } from "../data/values.ts";
import { type Schema, type Service, schemaOf, schemaOwner } from "../service/basic.ts";
import { Failed, type Functions, issueViolation, parseOutside } from "../service/functions.ts";
import { halt } from "../service/state.ts";

/** Lean's Seen, each map keyed by `<service>.<name>`, and the payloads by `<service>.<screen>.<control>`. */
export interface Seen {
  readonly words: readonly string[];
  readonly answers: ReadonlyMap<string, readonly Json[]>;
  readonly messages: ReadonlyMap<string, readonly Json[]>;
  readonly payloads: ReadonlyMap<string, readonly Json[]>;
}

export const nameOf = (r: { readonly service: string; readonly name: string }): string => `${r.service}.${r.name}`;

/** Lean's seenOf. */
export function seenOf(scenarios: readonly Scenario[]): Seen {
  const words = new Set<string>();
  const answers = new Map<string, Json[]>();
  const messages = new Map<string, Json[]>();
  const payloads = new Map<string, Json[]>();
  const add = (map: Map<string, Json[]>, key: string, value: Json) => {
    map.set(key, [...(map.get(key) ?? []), value]);
    for (const w of stringsOf(value)) words.add(w);
  };
  for (const sc of scenarios)
    for (const l of sc.lines)
      switch (l.type) {
        case "request":
          add(messages, nameOf(l.target), l.input.value as Json);
          break;
        case "emit":
          add(messages, nameOf(l.event), l.payload.value as Json);
          break;
        case "answer":
          if (l.request.type === "request") add(answers, nameOf(l.request.target), l.answer.value as Json);
          break;
        case "operate":
          if (l.screen.type === "screen")
            add(payloads, `${nameOf(l.screen.screen)}.${l.control}`, l.payload.value as Json);
          break;
      }
  return { words: [...words], answers, messages, payloads };
}

const fillerStrings = ["a", "b", "c"];
const representativeNumbers = [0, 1, 2, -1, 0.5, 10, 1000];
const representativeDates = ["2026-10-25", "2026-10-26"];
const representativeDateTimes = ["2026-10-25T00:00:00Z", "2026-10-26T00:00:00Z"];

type Schemaish = { readonly [key: string]: Json };

const isObject = (v: Json | undefined): v is Schemaish => typeof v === "object" && v !== null && !Array.isArray(v);

const pick = <T>(xs: readonly T[], i: number): T | undefined => (xs.length === 0 ? undefined : xs[i % xs.length]);

type Fits = (path: readonly SchemaStep[], value: Json) => boolean;

/** Lean's fitting. */
function fitting(fits: (value: Json) => boolean, candidates: readonly Json[], i: number): Json | undefined {
  const found: Json[] = [];
  for (const c of candidates) {
    if (!fits(c)) continue;
    if (found.length === i) return c;
    found.push(c);
  }
  return pick(found, i);
}

/** Lean's representative. */
function representative(
  fits: Fits,
  words: readonly string[],
  s: Json,
  path: readonly SchemaStep[],
  i: number,
): Json | undefined {
  if (!isObject(s)) return undefined;
  const { anyOf, oneOf, const: constant, enum: values, type } = s;
  const option = (options: readonly Json[], schemaOf: (o: Json) => Json): Json | undefined => {
    if (options.length === 0) return undefined;
    const index = i % options.length;
    return representative(fits, words, schemaOf(options[index] as Json), [...path, { kind: "option", index }], i);
  };
  if (Array.isArray(anyOf)) return option(anyOf, (o) => o);
  if (anyOf !== undefined) return undefined;
  if (Array.isArray(oneOf)) return option(oneOf, (o) => o);
  if (oneOf !== undefined) return undefined;
  if (constant !== undefined) return constant;
  if (Array.isArray(values)) return pick(values, i);
  if (Array.isArray(type)) return option(type, (t) => ({ ...s, type: t }));
  return typeof type === "string" ? typed(fits, words, s, path, type, i) : undefined;
}

function typed(
  fits: Fits,
  words: readonly string[],
  s: Schemaish,
  path: readonly SchemaStep[],
  type: string,
  i: number,
): Json | undefined {
  const fitsHere = (value: Json) => fits(path, value);
  switch (type) {
    case "null":
      return null;
    case "boolean":
      return i % 2 === 1;
    case "string":
      if (s["format"] === "date-time") return pick(representativeDateTimes, i);
      if (s["format"] === "date") return pick(representativeDates, i);
      return fitting(fitsHere, [...words, ...fillerStrings], i);
    case "number":
    case "integer":
      return fitting(fitsHere, representativeNumbers, i);
    case "array": {
      if (i === 0 || s["x-tazuna-sorted-by"] !== undefined) return [];
      const items = s["items"];
      const element =
        items === undefined ? undefined : representative(fits, words, items, [...path, { kind: "items" }], i - 1);
      return element === undefined ? [] : [element];
    }
    case "object": {
      const properties = s["properties"];
      if (!isObject(properties)) return {};
      const entries: [string, Json][] = [];
      for (const [k, p] of Object.entries(properties)) {
        const v = representative(fits, words, p, [...path, { kind: "field", name: k }], i);
        if (v === undefined) return undefined;
        entries.push([k, v]);
      }
      return Object.fromEntries(entries);
    }
    default:
      return undefined;
  }
}

/** Lean's distinct. */
export function distinct(values: readonly Json[]): Json[] {
  const kept = new Map<string, Json>();
  for (const v of values) if (!kept.has(canonicalJson(v))) kept.set(canonicalJson(v), v);
  return [...kept.values()];
}

/** Lean's valuesFor. A refinement that throws halts with the schema owner's fault. */
export function valuesFor(
  st: Service,
  fs: Functions,
  schema: Schema,
  listed: readonly Json[],
  words: readonly string[],
  n: number,
): Json[] {
  const json = expectFound(`schema ${JSON.stringify(schema)}`, schemaOf(st, schema) as Json | undefined);
  const fits: Fits = (path, value) => {
    const fit = fs.fits(schema, path, value);
    if (fit instanceof Failed) halt(issueViolation(schemaOwner(schema), fit));
    return fit;
  };
  let found = distinct(listed);
  const kept = new Set(found.map(canonicalJson));
  for (let i = 0; i < n + 2 && found.length < n; i += 1) {
    const v = representative(fits, words, json, [], i);
    if (v === undefined || kept.has(canonicalJson(v))) continue;
    const parsed = parseOutside(st, fs, schema, v);
    if (parsed instanceof Failed) halt(issueViolation(schemaOwner(schema), parsed));
    if (!("error" in parsed)) {
      found = [...found, v];
      kept.add(canonicalJson(v));
    }
  }
  return found.slice(0, n);
}
