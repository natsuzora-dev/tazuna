import { expectFound } from "../data/internalError.ts";
import type { Requester } from "../data/step.generated.ts";
import { canonicalJson, type Json } from "../data/values.ts";
import type { Processing } from "../service/chart/queue.ts";
import { exchanges } from "../service/input.ts";
import { copyId } from "../service/instance.ts";
import { sameLineId } from "../service/message.ts";
import { type Instance, keyCounts, machine } from "../service/state.ts";
import type { World } from "../sim/network.ts";

const byKey = ([a]: readonly [string, unknown], [b]: readonly [string, unknown]) => (a < b ? -1 : 1);

/** Lean's instanceValue. */
function instanceFingerprint(instance: Instance): unknown {
  return {
    id: instance.id,
    entered: [...instance.entered].map(([state, at]) => [state, at.toString()]),
    context: instance.context,
    held: [...instance.held],
    input: instance.input,
    lastChildren: [...instance.lastChildren],
    shown: [...instance.shown],
    closed: instance.closed,
  };
}

/** Lean's requestsValue. */
function requestsFingerprint(r: Processing): unknown {
  const s = r.state;
  const { lines } = s;
  const rank = (all: readonly number[], n: number) => new Set(all.filter((x) => x < n)).size;
  const traced = s.pending.map((p) => {
    const at = lines.findIndex((l) => l.dir === "out" && sameLineId(l.id, p.id));
    const line = expectFound(`request line of ${JSON.stringify(p.id)}`, lines[at]);
    return { p, time: line.time, before: lines.slice(0, at).filter((l) => l.dir === "in").length };
  });
  const turns = s.pending.map((p) => p.turn);
  const inputs = traced.map((t) => t.before);
  const requester = (q: Requester) =>
    q.kind === "automation" ? [q.automation] : [q.machine, q.kind === "state" ? q.state : q.slot];
  return {
    pending: traced.map(({ p, time, before }) => [
      p.id,
      p.activity.target,
      requester(p.requester),
      p.input,
      p.stale,
      rank(turns, p.turn),
      time,
      rank(inputs, before),
      lines.some((l) => "to" in l && sameLineId(l.to, p.id)),
    ]),
    queued: s.queued.map((q) => [q.machine, q.state, q.stale]),
  };
}

/** Lean's serviceFingerprint. */
function serviceFingerprint(r: Processing): string {
  const s = r.state;
  return canonicalJson({
    now: s.now.toString(),
    lineCounts: [...s.lineCounts].toSorted(byKey),
    keyCounts: keyCounts(s).toSorted(byKey),
    records: [
      ...[...s.records.keyed]
        .filter(([, rows]) => rows.size > 0)
        .map(([name, rows]): [string, unknown] => [
          name,
          [...rows].map(([key, row]): [string, unknown] => [key, row.encoded]).toSorted(byKey),
        ]),
      ...[...s.records.singles].map(([name, row]): [string, unknown] => [name, row.encoded]),
    ].toSorted(byKey),
    requests: requestsFingerprint(r),
    deadlines: s.deadlines.map((t) => [t.machine, t.state, t.name, t.time.toString()]),
    subscriptions: s.subscriptions.fingerprint(({ query, input }) => [query, input]),
    machines: [...s.machines.values()].map((instance) => [
      instanceFingerprint(instance),
      [...instance.copyKeys].map(([map, keys]) => [
        map,
        keys.flatMap((k) => {
          const copy = machine(s, copyId(instance.id, map, k));
          return copy === undefined ? [] : [instanceFingerprint(copy)];
        }),
      ]),
    ]),
    stack: s.stack,
    commandAnswers: [...s.commandAnswers]
      .toSorted(byKey)
      .map(([id, { request, answer }]) => [id, request.name, request.input, answer]),
    deliveries: [...s.deliveries].toSorted(),
    exchanges: exchanges(s)
      .map(({ id, target, sender, input, answers, events }) =>
        canonicalJson([id, target, sender, input, answers, events] as Json),
      )
      .toSorted(),
    started: s.started,
  });
}

export const halted = (w: World): boolean =>
  w.halted !== undefined || [...w.services.values()].some((p) => p.halted !== undefined);

/** Lean's worldFingerprint. */
export function worldFingerprint(w: World): string {
  if (halted(w)) return "halted";
  return canonicalJson([
    w.now.toString(),
    [...w.services].map(([service, p]) => [service, serviceFingerprint(p.processing)]),
    w.messages.flatMap((m) => (m.status === "inFlight" ? [[m.sender, m.receiver, m.body as never]] : [])),
  ]);
}
