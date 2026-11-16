import type { InvalidInput } from "../data/invalidInput.generated.ts";
import type { TraceLine } from "../data/trace.generated.ts";
import { type Bindings, bindNew } from "../data/trace.ts";
import { type Unified, unify, unifyAnswer } from "../data/unify.ts";
import {
  arrival,
  forPeer,
  inLines,
  type NamedForm,
  type PeerDerivation,
  type PeerOrigin,
  type Placed,
  peerArrivals,
  peerKeys,
  peerName,
  peerPlaced,
  peerTarget,
  rename,
  requestOf,
  unreached,
} from "./peer.ts";

const instant = (time: string) => Temporal.Instant.from(time);
const atOrBefore = (a: string, b: string) => Temporal.Instant.compare(instant(a), instant(b)) <= 0;

/** Lean's answersTo. */
function answersTo(lines: readonly TraceLine[], dir: "in" | "out", id: string) {
  return lines.flatMap((l) =>
    l.type === "answer" && l.dir === dir && l.to === id ? [{ time: l.time, answer: l.answer }] : [],
  );
}

type Checked = { readonly bindings: Bindings } | { readonly violation: InvalidInput };
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
  service: string,
  { peer, fromLines, peerForm, ownInputForm }: PeerDerivation,
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
  service: string,
  d: PeerDerivation,
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
    const checked = peerLine(service, d, created, back, lines, peerLines, before, bs, i, l);
    if ("violation" in checked) findings.push({ origin: { type: "line", line: i }, violation: checked.violation });
    else bs = checked.bindings;
    bindings.push(bs);
  });
  return { bindings, findings };
}
/** Lean's peerForward, from peerBindings of each line count (peerChecks). */
function peerForward(service: string, lines: readonly TraceLine[], bindings: readonly Bindings[], n: number): Bindings {
  const bound = [...(bindings[Math.min(n, lines.length)] as Bindings)].map(([k, v]) => [v, k] as const);
  // A Map keeps the last of equal keys, a Lean lookup the first: peerKeys come last here and first in Lean.
  return new Map([...bound, ...peerKeys(service, lines)]);
}

/** Lean's peerInputs. */
export function peerInputs(
  service: string,
  d: PeerDerivation,
  lines: readonly TraceLine[],
  peerLines: readonly TraceLine[],
): Placed[] {
  const { bindings } = peerChecks(service, d, peerArrivals(service, d, lines), lines, peerLines);
  const forward = (n: number) => peerForward(service, lines, bindings, n);
  const placed = peerPlaced(service, d, lines, forward);
  return [
    ...d.state.map((step) => ({ step, origin: { type: "given" } as PeerOrigin })),
    ...placed.map(({ step, origin }) =>
      origin.type === "elsewhere"
        ? { step: forPeer(forward(arrival(d.elsewhere, origin)), step), origin }
        : { step, origin },
    ),
  ];
}

/** Lean's peerFindings. */
export function peerFindings(
  service: string,
  d: PeerDerivation,
  arrivals: readonly number[],
  lines: readonly TraceLine[],
  peerLines: readonly TraceLine[],
  halted: readonly [PeerOrigin, string] | undefined,
): { readonly origin: PeerOrigin; readonly violation: InvalidInput }[] {
  if (halted !== undefined)
    return [
      {
        origin: halted[0],
        violation: { kind: "InvalidInput.haltedPeer", definition: null, data: { service: d.peer, halting: halted[1] } },
      },
    ];
  return peerChecks(service, d, arrivals, lines, peerLines).findings;
}

/**
 * Lean's peerRunFindings: the InvalidInput violations among `reported`, the violations of a peer's run that did not halt
 * with the origins of their inputs.
 */
export function peerRunFindings<V extends { readonly kind: string }>(
  reported: readonly { readonly origin: PeerOrigin; readonly violation: V }[],
): { readonly origin: PeerOrigin; readonly violation: V }[] {
  return reported.filter(({ violation }) => violation.kind.startsWith("InvalidInput."));
}
