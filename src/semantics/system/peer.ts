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

/** Lean's peerInputs. */
export function peerInputs(
  service: string,
  peer: string,
  state: readonly Step[],
  elsewhere: readonly (readonly [number, Step])[],
  lines: readonly TraceLine[],
): { readonly step: Step; readonly origin: Origin }[] {
  const keys = peerKeys(service, lines);
  const placed = Array.from({ length: lines.length + 1 }, (_, n) => {
    const others = elsewhere.flatMap(([p, step], index) =>
      p === n || (n === lines.length && n < p) ? [{ step, origin: { type: "elsewhere", index } as Origin }] : [],
    );
    const l = lines[n];
    const body = l === undefined ? undefined : peerBody(peer, lines, keys, l);
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
      origin.type === "elsewhere" ? { step: forPeer(keys, index, step), origin } : { step, origin },
    ),
  ];
}

const instant = (time: string) => Temporal.Instant.from(time);
const atOrBefore = (a: string, b: string) => Temporal.Instant.compare(instant(a), instant(b)) <= 0;

/** Lean's answersTo. */
function answersTo(lines: readonly TraceLine[], dir: "in" | "out", id: string) {
  return lines.flatMap((l) =>
    l.type === "answer" && l.dir === dir && l.to === id ? [{ time: l.time, answer: l.answer }] : [],
  );
}

const canonical = (v: unknown) => canonicalJson(v as Json);

type Normal = (value: unknown) => unknown;

/** The form of an output or payload of the peer's definition, by the peer's own name, that verify compares. */
export type PeerNormal = (name: string, value: unknown) => unknown;

/** Lean's sameAnswer. */
function sameAnswer(norm: Normal, seen: Normal, a: Answer, b: Answer): boolean {
  if (a.result === "rejected" || b.result === "rejected")
    return a.result === "rejected" && b.result === "rejected" && a.rejection.kind === b.rejection.kind;
  if (a.result !== b.result) return false;
  const [x, y] = ["output" in a ? a.output : undefined, "output" in b ? b.output : undefined];
  return x === undefined || y === undefined ? x === y : canonical(norm(x)) === canonical(norm(seen(y)));
}

/** Lean's emitted. */
const emitted = (norm: Normal, seen: Normal, event: string, payload: unknown, time: string, b: TraceLine) =>
  b.type === "event" &&
  b.dir === "out" &&
  b.name === event &&
  canonical(norm(seen(b.payload))) === canonical(norm(payload)) &&
  atOrBefore(b.time, time);

/** Lean's unify: `bs` is extended in place, and false means none. */
function unify(created: readonly string[], bs: Map<string, string>, a: unknown, b: unknown): boolean {
  if (typeof a === "string" && typeof b === "string") {
    const bound = bs.get(b);
    if (bound !== undefined) return bound === a;
    if (created.includes(b)) {
      if ([...bs.values()].includes(a)) return false;
      bs.set(b, a);
      return true;
    }
    return a === b;
  }
  if (Array.isArray(a) && Array.isArray(b))
    return a.length === b.length && a.every((x, i) => unify(created, bs, x, b[i]));
  if (
    a !== null &&
    b !== null &&
    typeof a === "object" &&
    typeof b === "object" &&
    !Array.isArray(a) &&
    !Array.isArray(b)
  ) {
    const [x, y] = [a as Record<string, unknown>, b as Record<string, unknown>];
    return (
      Object.keys(x).length === Object.keys(y).length &&
      Object.entries(x).every(([k, v]) => Object.hasOwn(y, k) && unify(created, bs, v, y[k]))
    );
  }
  return canonical(a) === canonical(b);
}

/** Lean's `unify ... |>.getD bs`: `bs` extended when the values unify, else `bs`. */
function unified(created: readonly string[], bs: Map<string, string>, a: unknown, b: unknown): Map<string, string> {
  const extended = new Map(bs);
  return unify(created, extended, a, b) ? extended : bs;
}

/** Lean's peerBindings. */
function peerBindings(
  normal: PeerNormal,
  peer: string,
  back: Bindings,
  aLines: readonly TraceLine[],
  bLines: readonly TraceLine[],
) {
  const created = bLines.flatMap((l) => l.created ?? []);
  let bs = new Map<string, string>();
  aLines.forEach((l, i) => {
    if (l.dir !== "in") return;
    if (l.type === "answer") {
      const target = peerTarget(peer, aLines, l.to);
      if (target === undefined || unreached(aLines, l.to)) return;
      const b = answersTo(bLines, "out", l.to)[answersTo(aLines.slice(0, i), "in", l.to).length];
      const [x, y] = [
        "output" in l.answer ? l.answer.output : undefined,
        b !== undefined && "output" in b.answer ? b.answer.output : undefined,
      ];
      if (x !== undefined && y !== undefined)
        bs = unified(created, bs, normal(target, x), normal(target, rename(back, y)));
    } else if (l.type === "event") {
      const n = peerName(peer, l.name);
      if (n === undefined) return;
      for (const b of bLines)
        if (b.type === "event" && b.dir === "out" && b.name === n && atOrBefore(b.time, l.time)) {
          const extended = new Map(bs);
          if (unify(created, extended, normal(n, l.payload), normal(n, rename(back, b.payload)))) {
            bs = extended;
            return;
          }
        }
    }
  });
  return bs;
}

/** Lean's peerSeen. */
function peerSeen(
  normal: PeerNormal,
  service: string,
  peer: string,
  aLines: readonly TraceLine[],
  bLines: readonly TraceLine[],
) {
  const back = new Map([...peerKeys(service, aLines)].map(([k, v]) => [v, k]));
  const bindings = new Map([...peerBindings(normal, peer, back, aLines, bLines), ...back]);
  return (v: unknown) => rename(bindings, v);
}

/** Lean's peerFinding. */
function peerFinding(
  normal: PeerNormal,
  peer: string,
  seen: (v: unknown) => unknown,
  aLines: readonly TraceLine[],
  bLines: readonly TraceLine[],
  i: number,
  l: TraceLine,
): InvalidInput | undefined {
  if (l.dir !== "in") return undefined;
  if (l.type === "answer") {
    const target = peerTarget(peer, aLines, l.to);
    if (target === undefined || unreached(aLines, l.to)) return undefined;
    const data = { requestId: l.to, target: { service: peer, name: target } };
    const b = answersTo(bLines, "out", l.to)[answersTo(aLines.slice(0, i), "in", l.to).length];
    if (b === undefined) return { kind: "InvalidInput.unansweredRequest", definition: null, data };
    return sameAnswer((v) => normal(target, v), seen, l.answer, b.answer) && atOrBefore(b.time, l.time)
      ? undefined
      : { kind: "InvalidInput.unproducibleAnswer", definition: null, data };
  }
  if (l.type === "event") {
    const n = peerName(peer, l.name);
    if (n === undefined || bLines.some((b) => emitted((v) => normal(n, v), seen, n, l.payload, l.time, b)))
      return undefined;
    return {
      kind: "InvalidInput.unproducibleEvent",
      definition: null,
      data: { eventId: l.id ?? "", event: { service: peer, name: n } },
    };
  }
  return undefined;
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
  const seen = peerSeen(normal, service, peer, aLines, bLines);
  return aLines.flatMap((l, i) => {
    const violation = peerFinding(normal, peer, seen, aLines, bLines, i, l);
    return violation === undefined ? [] : [{ origin: { type: "line", line: i } as Origin, violation }];
  });
}
