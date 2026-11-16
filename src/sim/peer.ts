import { mapOutput, unavailable } from "../data/answer.ts";
import type { Step } from "../data/step.generated.ts";
import type { TraceLine } from "../data/trace.generated.ts";
import { type Bindings, renamed } from "../data/trace.ts";
import type { Json } from "../data/values.ts";

/** Lean's peerKey. */
const peerKey = (service: string, key: string): string => `${service}.${key}`;

/** Lean's peerKeys. */
export const peerKeys = (service: string, lines: readonly TraceLine[]): Map<string, string> =>
  new Map(lines.flatMap((l) => l.created ?? []).map((k) => [k, peerKey(service, k)]));

/** Lean's peerName?. */
export const peerName = (peer: string, name: string): string | undefined =>
  name.startsWith(`${peer}.`) ? name.slice(peer.length + 1) : undefined;

/** Lean's unreached. */
export const unreached = (lines: readonly TraceLine[], id: string): boolean =>
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
export function peerTarget(peer: string, lines: readonly TraceLine[], id: string): string | undefined {
  const name = requestName(lines, id);
  return name === undefined ? undefined : peerName(peer, name);
}

export const rename = (keys: Bindings, value: unknown): unknown => renamed(keys, value as Json);

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

/** Lean's requestOf?. */
export const requestOf = (dir: "in" | "out", l: TraceLine) =>
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
  if (unavailable(l.answer)) return undefined;
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

/** Lean's peerInput?. */
function peerInput(
  service: string,
  peer: string,
  received: readonly string[],
  fromLines: readonly number[],
  lines: readonly TraceLine[],
  keys: Bindings,
  l: TraceLine,
): Body | undefined {
  return (
    peerBody(peer, lines, keys, l) ??
    peerEvent(service, received, keys, l) ??
    peerAnswer(service, lines, fromLines, keys, l)
  );
}

/** Lean's Step.Body.forPeer. */
export function forPeer(keys: Bindings, step: Step): Step {
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

/** Lean's NamedForm. */
export type NamedForm = (name: string, value: unknown) => unknown;

/** Lean's PeerDerivation. */
export interface PeerDerivation {
  readonly peer: string;
  readonly received: readonly string[];
  readonly fromLines: readonly number[];
  readonly state: readonly Step[];
  readonly elsewhere: readonly (readonly [number, Step])[];
  readonly peerForm: NamedForm;
  readonly ownInputForm: NamedForm;
}

/** Lean's inLines, as the places of the in lines. */
export const inLines = (lines: readonly TraceLine[]): number[] => lines.flatMap((l, j) => (l.dir === "in" ? [j] : []));

export type Placed = { readonly step: Step; readonly origin: PeerOrigin };

/** Lean's peerPlaced. */
export function peerPlaced(
  service: string,
  d: PeerDerivation,
  lines: readonly TraceLine[],
  keys: (n: number) => Bindings,
): Placed[] {
  return Array.from({ length: lines.length + 1 }, (_, n) => {
    const others = d.elsewhere.flatMap(([p, step], index): Placed[] =>
      p === n || (n === lines.length && n < p) ? [{ step, origin: { type: "elsewhere", index } }] : [],
    );
    const l = lines[n];
    const body = l === undefined ? undefined : peerInput(service, d.peer, d.received, d.fromLines, lines, keys(n), l);
    return l === undefined || body === undefined
      ? others
      : [...others, { step: { time: l.time, ...body } as Step, origin: { type: "line", line: n } as PeerOrigin }];
  }).flat();
}

/** Lean's PeerOrigin.arrival. */
export function arrival(elsewhere: readonly (readonly [number, Step])[], o: PeerOrigin): number {
  if (o.type === "line") return o.line;
  return o.type === "elsewhere" ? (elsewhere[o.index]?.[0] ?? 0) : 0;
}

/** Lean's peerArrivals. */
export function peerArrivals(service: string, d: PeerDerivation, lines: readonly TraceLine[]): number[] {
  return [
    ...d.state.map(() => 0),
    ...peerPlaced(service, d, lines, () => new Map()).map((p) => arrival(d.elsewhere, p.origin)),
  ];
}
