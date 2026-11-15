import { Bag, Runs } from "../../data/canonical.ts";
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
const peerName = (peer: string, name: string): string | undefined =>
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

/** Lean's peerTarget?. */
function peerTarget(peer: string, lines: readonly TraceLine[], id: string): string | undefined {
  for (const l of lines)
    if (l.dir === "out" && (l.type === "command" || l.type === "query" || l.type === "subscribe") && l.id === id) {
      const name = peerName(peer, l.name);
      if (name !== undefined) return name;
    }
  return undefined;
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
      if (l.id === undefined || unreached(lines, l.id)) return undefined;
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
  if (s instanceof Bag) return t instanceof Bag ? unifyBag(created, s.items, t.items, bs) : undefined;
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

/** Lean's unifyBag and unifyBagFrom. */
function unifyBag(
  created: ReadonlySet<string>,
  ss: readonly unknown[],
  ts: readonly unknown[],
  bs: Bindings,
): Bindings | undefined {
  if (ss.length !== ts.length) return undefined;
  const [first, ...rest] = ss;
  if (ss.length === 0) return bs;
  for (const [i, t] of ts.entries()) {
    const once = unify(created, first, t, bs);
    if (once === undefined) continue;
    const all = unifyBag(created, rest, ts.toSpliced(i, 1), once);
    if (all !== undefined) return all;
  }
  return undefined;
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

/** Lean's peerLine, with its lets as arguments. */
function peerLine(
  normal: PeerNormal,
  peer: string,
  created: ReadonlySet<string>,
  back: Bindings,
  aLines: readonly TraceLine[],
  bLines: readonly TraceLine[],
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
    const b = answersTo(bLines, "out", l.to)[answersTo(aLines.slice(0, i), "in", l.to).length];
    if (b === undefined) return { violation: { kind: "InvalidInput.unansweredRequest", definition: null, data } };
    const bindings = atOrBefore(b.time, l.time)
      ? unifyAnswer(created, seen(target), (v) => normal(target, v), bs, b.answer, l.answer)
      : undefined;
    return bindings === undefined
      ? { violation: { kind: "InvalidInput.unproducibleAnswer", definition: null, data } }
      : { bindings };
  }
  if (l.type === "event") {
    const n = peerName(peer, l.name);
    if (n === undefined) return { bindings: bs };
    for (const b of bLines)
      if (b.type === "event" && b.dir === "out" && b.name === n && atOrBefore(b.time, l.time)) {
        const bindings = unify(created, seen(n)(b.payload), normal(n, l.payload), bs);
        if (bindings !== undefined) return { bindings };
      }
    return {
      violation: {
        kind: "InvalidInput.unproducibleEvent",
        definition: null,
        data: { eventId: l.id ?? "", event: { service: peer, name: n } },
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
  aLines: readonly TraceLine[],
  bLines: readonly TraceLine[],
) {
  const created = new Set(bLines.flatMap((l) => l.created ?? []));
  const back = new Map([...peerKeys(service, aLines)].map(([k, v]) => [v, k]));
  let bs: Bindings = new Map();
  const bindings = [bs];
  const findings: { readonly origin: Origin; readonly violation: InvalidInput }[] = [];
  aLines.forEach((l, i) => {
    const checked = peerLine(normal, peer, created, back, aLines, bLines, bs, i, l);
    if ("violation" in checked) findings.push({ origin: { type: "line", line: i }, violation: checked.violation });
    else bs = checked.bindings;
    bindings.push(bs);
  });
  return { bindings, findings };
}

/** Lean's peerInputs. */
export function peerInputs(
  normal: PeerNormal,
  service: string,
  peer: string,
  state: readonly Step[],
  elsewhere: readonly (readonly [number, Step])[],
  aLines: readonly TraceLine[],
  bLines: readonly TraceLine[],
): { readonly step: Step; readonly origin: Origin }[] {
  const keys = peerKeys(service, aLines);
  const { bindings } = peerChecks(normal, service, peer, aLines, bLines);
  const forward = (n: number): Bindings =>
    new Map([...[...(bindings[Math.min(n, aLines.length)] as Bindings)].map(([k, v]) => [v, k] as const), ...keys]);
  const placed = Array.from({ length: aLines.length + 1 }, (_, n) => {
    const others = elsewhere.flatMap(([p, step], index) =>
      p === n || (n === aLines.length && n < p) ? [{ step, origin: { type: "elsewhere", index } as Origin }] : [],
    );
    const l = aLines[n];
    const body = l === undefined ? undefined : peerBody(peer, aLines, forward(n), l);
    return l === undefined || body === undefined
      ? others
      : [...others, { step: { time: l.time, ...body } as Step, origin: { type: "line", line: n } as Origin }];
  }).flat();
  const index = (r: number) => {
    if (r < state.length) return r;
    const found = placed.findIndex((p) => sameOrigin(p.origin, { type: "elsewhere", index: r - state.length }));
    return state.length + (found < 0 ? 0 : found);
  };
  return [
    ...state.map((step) => ({ step, origin: { type: "given" } as Origin })),
    ...placed.map(({ step, origin }) =>
      origin.type === "elsewhere"
        ? { step: forPeer(forward(elsewhere[origin.index]?.[0] ?? 0), index, step), origin }
        : { step, origin },
    ),
  ];
}

/** Lean's peerFindings. */
export function peerFindings(
  normal: PeerNormal,
  service: string,
  peer: string,
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
  return peerChecks(normal, service, peer, aLines, bLines).findings;
}
