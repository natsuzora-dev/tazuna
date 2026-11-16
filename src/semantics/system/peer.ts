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
        ? { type: "unsubscribe", subscription: { to: l.to } }
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

/** Lean's requestOf?. */
const requestOf = (dir: "in" | "out", l: TraceLine) =>
  l.dir === dir && (l.type === "command" || l.type === "query" || l.type === "subscribe") ? l : undefined;

/** Lean's peerAnswer?. */
function peerAnswer(
  service: string,
  lines: readonly TraceLine[],
  fromLines: readonly number[],
  keys: Bindings,
  l: TraceLine,
): Body | undefined {
  if (l.dir !== "out" || l.type !== "answer") return undefined;
  if ("rejection" in l.answer && l.answer.rejection.kind === "unavailable") return undefined;
  for (const k of fromLines) {
    const r = lines[k];
    const request = r === undefined ? undefined : requestOf("in", r);
    if (request?.id === l.to)
      return {
        type: "answerById",
        to: keys.get(l.to) ?? l.to,
        target: `${service}.${request.name}`,
        answer: mapOutput(l.answer, (v) => rename(keys, v)),
      };
  }
  return undefined;
}

/** Lean's Step.Body.forPeer. */
function forPeer(keys: Bindings, step: Step): Step {
  switch (step.type) {
    case "command":
    case "query":
    case "subscribe":
      return { ...step, input: rename(keys, step.input) };
    case "event":
      return { ...step, payload: rename(keys, step.payload) };
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

/** Lean's PeerOrigin. */
export type PeerOrigin =
  | { readonly type: "given" }
  | { readonly type: "line"; readonly line: number }
  | { readonly type: "elsewhere"; readonly index: number };

const instant = (time: string) => Temporal.Instant.from(time);
const atOrBefore = (a: string, b: string) => Temporal.Instant.compare(instant(a), instant(b)) <= 0;

/** Lean's answersTo. */
function answersTo(lines: readonly TraceLine[], dir: "in" | "out", id: string) {
  return lines.flatMap((l) =>
    l.type === "answer" && l.dir === dir && l.to === id ? [{ time: l.time, answer: l.answer }] : [],
  );
}

/** Lean's Bindings.bindNew. */
const bindNew = (bs: Bindings, v: string, w: string): Bindings | undefined =>
  bs.has(v) || [...bs.values()].includes(w) ? undefined : new Map([...bs, [v, w]]);

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

/** Lean's Unequal. */
type Unequal = "differ" | "searchLimit";

type Unified = Bindings | Unequal;

/** Lean's unify. */
function unify(created: ReadonlySet<string>, s: unknown, t: unknown, bs: Bindings): Unified {
  if (typeof s === "string") {
    if (typeof t !== "string") return "differ";
    if (created.has(s)) return bind(bs, s, t) ?? "differ";
    return t === s ? bs : "differ";
  }
  if (Array.isArray(s)) return Array.isArray(t) && s.length === t.length ? unifyList(created, s, t, bs) : "differ";
  if (s instanceof Runs)
    return t instanceof Runs && s.runs.length === t.runs.length ? unifyList(created, s.runs, t.runs, bs) : "differ";
  if (s instanceof Bag) {
    if (!(t instanceof Bag) || !bagFits(created, s.items, t.items)) return "differ";
    const found = unifyBag(created, s.items, t.items, bs, searchLimit);
    if ("bindings" in found) return found.bindings;
    return found.left === 0 ? "searchLimit" : "differ";
  }
  if (isObject(s)) {
    if (!isObject(t) || !sameKeys(s, t)) return "differ";
    return unifyList(
      created,
      Object.values(s),
      Object.keys(s).map((k) => t[k]),
      bs,
    );
  }
  return s === t ? bs : "differ";
}

/** Lean's unifyList and unifyFields. */
function unifyList(
  created: ReadonlySet<string>,
  xs: readonly unknown[],
  ys: readonly unknown[],
  bs: Bindings,
): Unified {
  let bindings: Unified = bs;
  for (const [i, x] of xs.entries()) {
    if (typeof bindings === "string") return bindings;
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
    if (once === "searchLimit") return { left: 0 };
    if (once === "differ") continue;
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
): Unified {
  if (b.result === "rejected" || a.result === "rejected")
    return b.result === "rejected" && a.result === "rejected" && b.rejection.kind === a.rejection.kind ? bs : "differ";
  if (b.result !== a.result) return "differ";
  const [x, y] = ["output" in b ? b.output : undefined, "output" in a ? a.output : undefined];
  return x === undefined || y === undefined ? (x === y ? bs : "differ") : unify(created, seen(x), form(y), bs);
}

/** The form of an output or payload of the peer's definition, by the peer's own name, that verify compares. */
export type NamedForm = (name: string, value: unknown) => unknown;

type Checked = { readonly bindings: Bindings } | { readonly violation: InvalidInput };

/** Lean's inLines, as the places of the in lines. */
const inLines = (lines: readonly TraceLine[]): number[] => lines.flatMap((l, j) => (l.dir === "in" ? [j] : []));

/** Lean's peerBefore, with the inLines of `peerLines` as an argument. */
function peerBefore(arrivals: readonly number[], peerIns: readonly number[], peerLength: number, i: number): number {
  const k = arrivals.findIndex((a) => i < a);
  return k < 0 ? peerLength : (peerIns[k] ?? peerLength);
}

/** Lean's sentAs?. */
function sentAs(
  created: ReadonlySet<string>,
  seen: NamedForm,
  form: NamedForm,
  service: string,
  bs: Bindings,
  l: TraceLine,
  b: TraceLine,
): Unified | undefined {
  if (!atOrBefore(b.time, l.time)) return undefined;
  if (l.dir === "in" && l.type === "unsubscribe" && b.dir === "out" && b.type === "unsubscribe")
    return bs.get(b.to) === l.to ? bindNew(bs, b.id, l.id) : undefined;
  const [x, y] = [requestOf("in", l), requestOf("out", b)];
  if (x === undefined || y === undefined || y.type !== x.type || peerName(service, y.name) !== x.name) return undefined;
  const bound = bindNew(bs, y.id, x.id);
  return bound === undefined ? undefined : unify(created, seen(x.name, y.input), form(x.name, x.input), bound);
}

/** Lean's peerSent, without the place of the line. */
function peerSent(
  created: ReadonlySet<string>,
  seen: NamedForm,
  form: NamedForm,
  service: string,
  bs: Bindings,
  before: readonly TraceLine[],
  l: TraceLine,
): Unified {
  let limited = false;
  for (const b of before) {
    const sent = sentAs(created, seen, form, service, bs, l, b);
    if (sent === undefined) continue;
    if (typeof sent !== "string") return sent;
    limited ||= sent === "searchLimit";
  }
  return limited ? "searchLimit" : "differ";
}

const searchLimitAt = (l: TraceLine, peer: string): Checked => ({
  violation: { kind: "InvalidInput.peerSearchLimit", definition: null, data: { lineId: l.id, service: peer } },
});

/** Lean's peerLine, with its lets as arguments. */
function peerLine(
  peerForm: NamedForm,
  ownInputForm: NamedForm,
  service: string,
  peer: string,
  fromLines: readonly number[],
  created: ReadonlySet<string>,
  back: Bindings,
  lines: readonly TraceLine[],
  peerLines: readonly TraceLine[],
  before: readonly TraceLine[],
  bs: Bindings,
  i: number,
  l: TraceLine,
): Checked {
  const seen = (n: string) => (v: unknown) => peerForm(n, rename(back, v));
  if (l.dir !== "in") return { bindings: bs };
  if (
    (l.type === "command" || l.type === "query" || l.type === "subscribe" || l.type === "unsubscribe") &&
    fromLines.includes(i)
  ) {
    const seenInput = (n: string, v: unknown) => ownInputForm(n, rename(back, v));
    const sent = peerSent(created, seenInput, ownInputForm, service, bs, before, l);
    if (sent === "searchLimit") return searchLimitAt(l, peer);
    if (sent === "differ")
      return {
        violation: {
          kind: "InvalidInput.unproducibleRequest",
          definition: null,
          data: { requestId: l.id, service: peer },
        },
      };
    return { bindings: sent };
  }
  if (l.type === "answer") {
    const target = peerTarget(peer, lines, l.to);
    if (target === undefined || unreached(lines, l.to)) return { bindings: bs };
    const data = { requestId: l.to, target: { service: peer, name: target } };
    const k = answersTo(lines.slice(0, i), "in", l.to).length;
    if (answersTo(peerLines, "out", l.to)[k] === undefined)
      return { violation: { kind: "InvalidInput.unansweredRequest", definition: null, data } };
    const b = answersTo(before, "out", l.to)[k];
    const bindings =
      b !== undefined && atOrBefore(b.time, l.time)
        ? unifyAnswer(created, seen(target), (v) => peerForm(target, v), bs, b.answer, l.answer)
        : "differ";
    if (bindings === "searchLimit") return searchLimitAt(l, peer);
    return bindings === "differ"
      ? { violation: { kind: "InvalidInput.unproducibleAnswer", definition: null, data } }
      : { bindings };
  }
  if (l.type === "event") {
    const n = peerName(peer, l.name);
    if (n === undefined) return { bindings: bs };
    let limited = false;
    for (const b of before)
      if (
        b.type === "event" &&
        b.dir === "out" &&
        b.name === n &&
        atOrBefore(b.time, l.time) &&
        (l.resultOf === undefined || b.resultOf === l.resultOf)
      ) {
        const bindings = unify(created, seen(n)(b.payload), peerForm(n, l.payload), bs);
        if (typeof bindings !== "string") return { bindings };
        limited ||= bindings === "searchLimit";
      }
    if (limited) return searchLimitAt(l, peer);
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
  peerForm: NamedForm,
  ownInputForm: NamedForm,
  service: string,
  peer: string,
  fromLines: readonly number[],
  arrivals: readonly number[],
  lines: readonly TraceLine[],
  peerLines: readonly TraceLine[],
) {
  const created = new Set(peerLines.flatMap((l) => l.created ?? []));
  const back = new Map([...peerKeys(service, lines)].map(([k, v]) => [v, k]));
  const peerIns = inLines(peerLines);
  let bs: Bindings = new Map();
  const bindings = [bs];
  const findings: { readonly origin: PeerOrigin; readonly violation: InvalidInput }[] = [];
  lines.forEach((l, i) => {
    const before = peerLines.slice(0, peerBefore(arrivals, peerIns, peerLines.length, i));
    const checked = peerLine(
      peerForm,
      ownInputForm,
      service,
      peer,
      fromLines,
      created,
      back,
      lines,
      peerLines,
      before,
      bs,
      i,
      l,
    );
    if ("violation" in checked) findings.push({ origin: { type: "line", line: i }, violation: checked.violation });
    else bs = checked.bindings;
    bindings.push(bs);
  });
  return { bindings, findings };
}

type Placed = { readonly step: Step; readonly origin: PeerOrigin };

/** Lean's peerPlaced. */
function peerPlaced(
  service: string,
  peer: string,
  received: readonly string[],
  fromLines: readonly number[],
  elsewhere: readonly (readonly [number, Step])[],
  lines: readonly TraceLine[],
  keys: (n: number) => Bindings,
): Placed[] {
  return Array.from({ length: lines.length + 1 }, (_, n) => {
    const others = elsewhere.flatMap(([p, step], index): Placed[] =>
      p === n || (n === lines.length && n < p) ? [{ step, origin: { type: "elsewhere", index } }] : [],
    );
    const l = lines[n];
    const body =
      l === undefined
        ? undefined
        : (peerBody(peer, lines, keys(n), l) ??
          peerEvent(service, received, keys(n), l) ??
          peerAnswer(service, lines, fromLines, keys(n), l));
    return l === undefined || body === undefined
      ? others
      : [...others, { step: { time: l.time, ...body } as Step, origin: { type: "line", line: n } as PeerOrigin }];
  }).flat();
}

/** Lean's PeerOrigin.arrival. */
function arrival(elsewhere: readonly (readonly [number, Step])[], o: PeerOrigin): number {
  if (o.type === "line") return o.line;
  return o.type === "elsewhere" ? (elsewhere[o.index]?.[0] ?? 0) : 0;
}

/** Lean's peerArrivals. */
export function peerArrivals(
  service: string,
  peer: string,
  received: readonly string[],
  fromLines: readonly number[],
  state: readonly Step[],
  elsewhere: readonly (readonly [number, Step])[],
  lines: readonly TraceLine[],
): number[] {
  return [
    ...state.map(() => 0),
    ...peerPlaced(service, peer, received, fromLines, elsewhere, lines, () => new Map()).map((p) =>
      arrival(elsewhere, p.origin),
    ),
  ];
}

/** Lean's peerInputs. */
export function peerInputs(
  peerForm: NamedForm,
  ownInputForm: NamedForm,
  service: string,
  peer: string,
  received: readonly string[],
  fromLines: readonly number[],
  state: readonly Step[],
  elsewhere: readonly (readonly [number, Step])[],
  lines: readonly TraceLine[],
  peerLines: readonly TraceLine[],
): Placed[] {
  const keys = peerKeys(service, lines);
  const arrivals = peerArrivals(service, peer, received, fromLines, state, elsewhere, lines);
  const { bindings } = peerChecks(peerForm, ownInputForm, service, peer, fromLines, arrivals, lines, peerLines);
  const forward = (n: number): Bindings =>
    new Map([...[...(bindings[Math.min(n, lines.length)] as Bindings)].map(([k, v]) => [v, k] as const), ...keys]);
  const placed = peerPlaced(service, peer, received, fromLines, elsewhere, lines, forward);
  return [
    ...state.map((step) => ({ step, origin: { type: "given" } as PeerOrigin })),
    ...placed.map(({ step, origin }) =>
      origin.type === "elsewhere"
        ? { step: forPeer(forward(arrival(elsewhere, origin)), step), origin }
        : { step, origin },
    ),
  ];
}

/** Lean's peerFindings. */
export function peerFindings(
  peerForm: NamedForm,
  ownInputForm: NamedForm,
  service: string,
  peer: string,
  fromLines: readonly number[],
  arrivals: readonly number[],
  lines: readonly TraceLine[],
  peerLines: readonly TraceLine[],
  halted: readonly [PeerOrigin, string] | undefined,
): { readonly origin: PeerOrigin; readonly violation: InvalidInput }[] {
  if (halted !== undefined)
    return [
      {
        origin: halted[0],
        violation: { kind: "InvalidInput.haltedPeer", definition: null, data: { service: peer, halting: halted[1] } },
      },
    ];
  return peerChecks(peerForm, ownInputForm, service, peer, fromLines, arrivals, lines, peerLines).findings;
}
