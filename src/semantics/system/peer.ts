import { Bag, Runs, searchLimit } from "../../data/canonical.ts";
import type { InvalidInput } from "../../data/invalidInput.generated.ts";
import type { Step } from "../../data/step.generated.ts";
import type { Answer, TraceLine } from "../../data/trace.generated.ts";
import { type Bindings, renamed } from "../../data/trace.ts";
import { canonicalJson, type Json } from "../../data/values.ts";

/** Lean's peerKey. */
const peerKey = (service: string, key: string): string => `${service}.${key}`;

/** Lean's peerKeys. */
const peerKeys = (service: string, lines: readonly TraceLine[]): Map<string, string> =>
  new Map(lines.flatMap((l) => l.created ?? []).map((k) => [k, peerKey(service, k)]));

/** Lean's peerName?. */
export const peerName = (peer: string, name: string): string | undefined =>
  name.startsWith(`${peer}.`) ? name.slice(peer.length + 1) : undefined;

/** Lean's unreached. */
const unreached = (lines: readonly TraceLine[], id: string): boolean =>
  lines.some(
    (l) =>
      l.dir === "in" &&
      l.type === "answer" &&
      l.to === id &&
      "rejection" in l.answer &&
      l.answer.rejection.kind === "unavailable",
  );

/** Lean's requestName?. */
function requestName(lines: readonly TraceLine[], id: string): string | undefined {
  for (const l of lines)
    if (l.dir === "out" && (l.type === "command" || l.type === "query" || l.type === "subscribe") && l.id === id)
      return l.name;
  return undefined;
}

/** Lean's peerTarget?. */
function peerTarget(peer: string, lines: readonly TraceLine[], id: string): string | undefined {
  const name = requestName(lines, id);
  return name === undefined ? undefined : peerName(peer, name);
}

const rename = (keys: Bindings, value: unknown): unknown => renamed(keys, value as Json);

type Body = Step extends infer S ? (S extends Step ? Omit<S, "time" | "deadlineOrder" | "stepOrder"> : never) : never;

/** Lean's peerBody?. */
function peerBody(peer: string, lines: readonly TraceLine[], keys: Bindings, l: TraceLine): Body | undefined {
  if (l.dir !== "out") return undefined;
  switch (l.type) {
    case "command":
    case "query":
    case "subscribe": {
      if (unreached(lines, l.id)) return undefined;
      const name = peerName(peer, l.name);
      return name === undefined ? undefined : { type: l.type, id: l.id, name, input: rename(keys, l.input) };
    }
    case "unsubscribe":
      return peerTarget(peer, lines, l.to) !== undefined && !unreached(lines, l.to)
        ? { type: "unsubscribe", to: l.to }
        : undefined;
    default:
      return undefined;
  }
}

/** Lean's peerEvent?. */
export function peerEvent(
  service: string,
  received: readonly string[],
  keys: Bindings,
  l: TraceLine,
): Body | undefined {
  if (l.dir !== "out" || l.type !== "event") return undefined;
  const name = received.find((r) => peerName(service, r) === l.name);
  return name === undefined ? undefined : { type: "event", id: l.id, name, payload: rename(keys, l.payload) };
}

const mapOutput = (answer: Answer, f: (v: unknown) => unknown): Answer =>
  "output" in answer ? ({ ...answer, output: f(answer.output) } as Answer) : answer;

/** Lean's Step.Body.forPeer. */
function forPeer(keys: Bindings, index: (r: number) => number, step: Step): Step {
  switch (step.type) {
    case "command":
    case "query":
    case "subscribe":
      return { ...step, input: rename(keys, step.input) };
    case "event":
      return {
        ...step,
        payload: rename(keys, step.payload),
        ...(step.resultOf === undefined ? {} : { resultOf: index(step.resultOf) }),
      };
    case "operation":
    case "unacceptedOperation":
      return { ...step, payload: rename(keys, step.payload) };
    case "answer": {
      const { choice } = step;
      return {
        ...step,
        answer: mapOutput(step.answer, (v) => rename(keys, v)),
        ...(choice === undefined || !("input" in choice) || choice.input === undefined
          ? {}
          : { choice: { ...choice, input: rename(keys, choice.input) } }),
      };
    }
    default:
      return step;
  }
}

/** Lean's requestOfLine?. */
const requestOfLine = (lines: readonly TraceLine[], j: number): string | undefined =>
  lines.slice(0, j + 1).findLast((l) => l.dir === "in")?.id;

/** Lean's Origin. */
export type Origin =
  | { readonly type: "given" }
  | { readonly type: "line"; readonly line: number }
  | { readonly type: "elsewhere"; readonly index: number };

const sameOrigin = (a: Origin, b: Origin) => canonicalJson(a) === canonicalJson(b);

const instant = (time: string) => Temporal.Instant.from(time);
const atOrBefore = (a: string, b: string) => Temporal.Instant.compare(instant(a), instant(b)) <= 0;

/** Lean's answersTo. */
function answersTo(lines: readonly TraceLine[], dir: "in" | "out", id: string) {
  return lines.flatMap((l) =>
    l.type === "answer" && l.dir === dir && l.to === id ? [{ time: l.time, answer: l.answer }] : [],
  );
}

/** Lean's Bindings.bind. */
function bind(bs: Bindings, v: string, w: string): Bindings | undefined {
  const x = bs.get(v);
  if (x !== undefined) return x === w ? bs : undefined;
  return [...bs.values()].includes(w) ? undefined : new Map([...bs, [v, w]]);
}

const isObject = (v: unknown): v is Record<string, unknown> =>
  v !== null && typeof v === "object" && !Array.isArray(v) && !(v instanceof Bag) && !(v instanceof Runs);

const sameKeys = (s: Record<string, unknown>, t: Record<string, unknown>): boolean =>
  canonicalJson(Object.keys(s).toSorted()) === canonicalJson(Object.keys(t).toSorted());

/** Lean's unify. */
function unify(created: ReadonlySet<string>, s: unknown, t: unknown, bs: Bindings): Bindings | undefined {
  if (typeof s === "string") {
    if (typeof t !== "string") return undefined;
    if (created.has(s)) return bind(bs, s, t);
    return t === s ? bs : undefined;
  }
  if (Array.isArray(s)) return Array.isArray(t) && s.length === t.length ? unifyList(created, s, t, bs) : undefined;
  if (s instanceof Runs)
    return t instanceof Runs && s.runs.length === t.runs.length ? unifyList(created, s.runs, t.runs, bs) : undefined;
  if (s instanceof Bag) {
    if (!(t instanceof Bag) || !bagFits(created, s.items, t.items)) return undefined;
    const found = unifyBag(created, s.items, t.items, bs, searchLimit);
    return "bindings" in found ? found.bindings : undefined;
  }
  if (isObject(s)) {
    if (!isObject(t) || !sameKeys(s, t)) return undefined;
    return unifyList(
      created,
      Object.values(s),
      Object.keys(s).map((k) => t[k]),
      bs,
    );
  }
  return s === t ? bs : undefined;
}

/** Lean's unifyList and unifyFields. */
function unifyList(
  created: ReadonlySet<string>,
  xs: readonly unknown[],
  ys: readonly unknown[],
  bs: Bindings,
): Bindings | undefined {
  let bindings: Bindings | undefined = bs;
  for (const [i, x] of xs.entries()) {
    if (bindings === undefined) return undefined;
    bindings = unify(created, x, ys[i], bindings);
  }
  return bindings;
}

/** Lean's fits, fitsList and fitsFields. */
function fits(created: ReadonlySet<string>, s: unknown, t: unknown): boolean {
  if (typeof s === "string") return typeof t === "string" && (created.has(s) || t === s);
  const all = (xs: readonly unknown[], ys: readonly unknown[]) =>
    xs.length === ys.length && xs.every((x, i) => fits(created, x, ys[i]));
  if (Array.isArray(s)) return Array.isArray(t) && all(s, t);
  if (s instanceof Runs) return t instanceof Runs && all(s.runs, t.runs);
  if (s instanceof Bag) return t instanceof Bag && s.items.length === t.items.length;
  if (isObject(s)) return isObject(t) && sameKeys(s, t) && Object.keys(s).every((k) => fits(created, s[k], t[k]));
  return s === t;
}

/** Lean's bagFits. */
function bagFits(created: ReadonlySet<string>, ss: readonly unknown[], ts: readonly unknown[]): boolean {
  const fitting = ss.map((s) => ts.flatMap((t, k) => (fits(created, s, t) ? [k] : [])));
  const keys = fitting.map((ks) => ks.join(","));
  return keys.every((key, i) => keys.filter((k) => k === key).length <= (fitting[i] as number[]).length);
}

type Search = { readonly bindings: Bindings } | { readonly left: number };

/** Lean's unifyBag and unifyBagFrom. */
function unifyBag(
  created: ReadonlySet<string>,
  ss: readonly unknown[],
  ts: readonly unknown[],
  bs: Bindings,
  left: number,
): Search {
  if (ss.length !== ts.length) return { left };
  const [first, ...rest] = ss;
  if (ss.length === 0) return { bindings: bs };
  let tries = left;
  for (const [i, t] of ts.entries()) {
    if (tries === 0) return { left: 0 };
    tries -= 1;
    const once = unify(created, first, t, bs);
    if (once === undefined) continue;
    const all = unifyBag(created, rest, ts.toSpliced(i, 1), once, tries);
    if ("bindings" in all) return all;
    tries = all.left;
  }
  return { left: tries };
}

type Form = (value: unknown) => unknown;

/** Lean's unifyAnswer. */
function unifyAnswer(
  created: ReadonlySet<string>,
  seen: Form,
  form: Form,
  bs: Bindings,
  b: Answer,
  a: Answer,
): Bindings | undefined {
  if (b.result === "rejected" || a.result === "rejected")
    return b.result === "rejected" && a.result === "rejected" && b.rejection.kind === a.rejection.kind ? bs : undefined;
  if (b.result !== a.result) return undefined;
  const [x, y] = ["output" in b ? b.output : undefined, "output" in a ? a.output : undefined];
  return x === undefined || y === undefined ? (x === y ? bs : undefined) : unify(created, seen(x), form(y), bs);
}

/** The form of an output or payload of the peer's definition, by the peer's own name, that verify compares. */
export type PeerNormal = (name: string, value: unknown) => unknown;

type Checked = { readonly bindings: Bindings } | { readonly violation: InvalidInput };

/** Lean's inLines, as the places of the in lines. */
const inLines = (lines: readonly TraceLine[]): number[] => lines.flatMap((l, j) => (l.dir === "in" ? [j] : []));

/** Lean's peerBefore, with the inLines of `bLines` as an argument. */
function peerBefore(arrivals: readonly number[], bIns: readonly number[], bLength: number, i: number): number {
  const k = arrivals.findIndex((a) => i < a);
  return k < 0 ? bLength : (bIns[k] ?? bLength);
}

/** Lean's peerLine, with its lets as arguments. */
function peerLine(
  normal: PeerNormal,
  peer: string,
  created: ReadonlySet<string>,
  back: Bindings,
  aLines: readonly TraceLine[],
  bLines: readonly TraceLine[],
  before: readonly TraceLine[],
  bs: Bindings,
  i: number,
  l: TraceLine,
): Checked {
  const seen = (n: string) => (v: unknown) => normal(n, rename(back, v));
  if (l.dir !== "in") return { bindings: bs };
  if (l.type === "answer") {
    const target = peerTarget(peer, aLines, l.to);
    if (target === undefined || unreached(aLines, l.to)) return { bindings: bs };
    const data = { requestId: l.to, target: { service: peer, name: target } };
    const k = answersTo(aLines.slice(0, i), "in", l.to).length;
    if (answersTo(bLines, "out", l.to)[k] === undefined)
      return { violation: { kind: "InvalidInput.unansweredRequest", definition: null, data } };
    const b = answersTo(before, "out", l.to)[k];
    const bindings =
      b !== undefined && atOrBefore(b.time, l.time)
        ? unifyAnswer(created, seen(target), (v) => normal(target, v), bs, b.answer, l.answer)
        : undefined;
    return bindings === undefined
      ? { violation: { kind: "InvalidInput.unproducibleAnswer", definition: null, data } }
      : { bindings };
  }
  if (l.type === "event") {
    const n = peerName(peer, l.name);
    if (n === undefined) return { bindings: bs };
    for (const [j, b] of before.entries())
      if (
        b.type === "event" &&
        b.dir === "out" &&
        b.name === n &&
        atOrBefore(b.time, l.time) &&
        (l.resultOf === undefined || requestOfLine(bLines, j) === l.resultOf)
      ) {
        const bindings = unify(created, seen(n)(b.payload), normal(n, l.payload), bs);
        if (bindings !== undefined) return { bindings };
      }
    return {
      violation: {
        kind: "InvalidInput.unproducibleEvent",
        definition: null,
        data: { eventId: l.id, event: { service: peer, name: n } },
      },
    };
  }
  return { bindings: bs };
}

/**
 * Lean's peerBindings for each line count from 0 to the run's length, and the violations of peerFindings of a run that
 * did not halt, in one pass over the run.
 */
function peerChecks(
  normal: PeerNormal,
  service: string,
  peer: string,
  arrivals: readonly number[],
  aLines: readonly TraceLine[],
  bLines: readonly TraceLine[],
) {
  const created = new Set(bLines.flatMap((l) => l.created ?? []));
  const back = new Map([...peerKeys(service, aLines)].map(([k, v]) => [v, k]));
  const bIns = inLines(bLines);
  let bs: Bindings = new Map();
  const bindings = [bs];
  const findings: { readonly origin: Origin; readonly violation: InvalidInput }[] = [];
  aLines.forEach((l, i) => {
    const before = bLines.slice(0, peerBefore(arrivals, bIns, bLines.length, i));
    const checked = peerLine(normal, peer, created, back, aLines, bLines, before, bs, i, l);
    if ("violation" in checked) findings.push({ origin: { type: "line", line: i }, violation: checked.violation });
    else bs = checked.bindings;
    bindings.push(bs);
  });
  return { bindings, findings };
}

type Placed = { readonly step: Step; readonly origin: Origin };

/** Lean's peerPlaced. */
function peerPlaced(
  service: string,
  peer: string,
  received: readonly string[],
  elsewhere: readonly (readonly [number, Step])[],
  aLines: readonly TraceLine[],
  keys: (n: number) => Bindings,
): Placed[] {
  return Array.from({ length: aLines.length + 1 }, (_, n) => {
    const others = elsewhere.flatMap(([p, step], index): Placed[] =>
      p === n || (n === aLines.length && n < p) ? [{ step, origin: { type: "elsewhere", index } }] : [],
    );
    const l = aLines[n];
    const body =
      l === undefined ? undefined : (peerBody(peer, aLines, keys(n), l) ?? peerEvent(service, received, keys(n), l));
    return l === undefined || body === undefined
      ? others
      : [...others, { step: { time: l.time, ...body } as Step, origin: { type: "line", line: n } as Origin }];
  }).flat();
}

/** Lean's Origin.arrival. */
function arrival(elsewhere: readonly (readonly [number, Step])[], o: Origin): number {
  if (o.type === "line") return o.line;
  return o.type === "elsewhere" ? (elsewhere[o.index]?.[0] ?? 0) : 0;
}

/** Lean's peerArrivals. */
export function peerArrivals(
  service: string,
  peer: string,
  received: readonly string[],
  state: readonly Step[],
  elsewhere: readonly (readonly [number, Step])[],
  aLines: readonly TraceLine[],
): number[] {
  return [
    ...state.map(() => 0),
    ...peerPlaced(service, peer, received, elsewhere, aLines, () => new Map()).map((p) => arrival(elsewhere, p.origin)),
  ];
}

/** Lean's peerInputs. */
export function peerInputs(
  normal: PeerNormal,
  service: string,
  peer: string,
  received: readonly string[],
  state: readonly Step[],
  elsewhere: readonly (readonly [number, Step])[],
  aLines: readonly TraceLine[],
  bLines: readonly TraceLine[],
): Placed[] {
  const keys = peerKeys(service, aLines);
  const arrivals = peerArrivals(service, peer, received, state, elsewhere, aLines);
  const { bindings } = peerChecks(normal, service, peer, arrivals, aLines, bLines);
  const forward = (n: number): Bindings =>
    new Map([...[...(bindings[Math.min(n, aLines.length)] as Bindings)].map(([k, v]) => [v, k] as const), ...keys]);
  const placed = peerPlaced(service, peer, received, elsewhere, aLines, forward);
  const index = (r: number) => {
    if (r < state.length) return r;
    const found = placed.findIndex((p) => sameOrigin(p.origin, { type: "elsewhere", index: r - state.length }));
    return state.length + (found < 0 ? 0 : found);
  };
  return [
    ...state.map((step) => ({ step, origin: { type: "given" } as Origin })),
    ...placed.map(({ step, origin }) =>
      origin.type === "elsewhere"
        ? { step: forPeer(forward(arrival(elsewhere, origin)), index, step), origin }
        : { step, origin },
    ),
  ];
}

/** Lean's peerFindings. */
export function peerFindings(
  normal: PeerNormal,
  service: string,
  peer: string,
  arrivals: readonly number[],
  aLines: readonly TraceLine[],
  bLines: readonly TraceLine[],
  halted: readonly [Origin, string] | undefined,
): { readonly origin: Origin; readonly violation: InvalidInput }[] {
  if (halted !== undefined)
    return [
      {
        origin: halted[0],
        violation: { kind: "InvalidInput.haltedPeer", definition: null, data: { service: peer, halting: halted[1] } },
      },
    ];
  return peerChecks(normal, service, peer, arrivals, aLines, bLines).findings;
}
