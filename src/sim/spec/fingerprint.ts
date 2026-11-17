import { canonicalJson } from "../../data/values.ts";
import type { Processing } from "../../service/chart/queue.ts";
import { copyId } from "../../service/instance.ts";
import { type Instance, keyCounts, machine, type Requester } from "../../service/state.ts";

const byKey = ([a]: readonly [string, unknown], [b]: readonly [string, unknown]) => (a < b ? -1 : 1);

function instanceFingerprint(instance: Instance): unknown {
  const { opener } = instance;
  return {
    id: instance.id,
    entered: [...instance.entered].map(([state, at]) => [state, at.toString()]),
    context: instance.context,
    input: instance.input,
    lastChildren: [...instance.lastChildren],
    shown: [...instance.shown],
    closed: instance.closed,
    opener: opener === undefined ? null : [opener.parent, opener.state, opener.key],
  };
}

/**
 * Returns the pending requests and, for each, what alikeTo reads from the trace: the time of the request line, the
 * number of input lines before it, and whether a line names it. Only the order of the turns and of the input-line
 * counts is read.
 */
function requestsFingerprint(r: Processing): unknown {
  const s = r.state;
  const { lines } = s;
  const rank = (all: readonly number[], n: number) => new Set(all.filter((x) => x < n)).size;
  const inputsBefore = (id: string) => {
    const at = lines.findIndex((l) => l.dir === "out" && l.id === id);
    return { time: lines[at]?.time ?? null, inputs: lines.slice(0, at).filter((l) => l.dir === "in").length };
  };
  const traced = s.pending.map((p) => inputsBefore(p.id));
  const turns = s.pending.map((p) => p.turn);
  const requester = (q: Requester) =>
    q.kind === "automation" ? [q.automation] : [q.machine, q.kind === "state" ? q.state : q.slot];
  return {
    pending: s.pending.map((p, i) => [
      p.id,
      p.activity.target,
      requester(p.requester),
      p.input,
      p.stale,
      rank(turns, turns[i] ?? 0),
      traced[i]?.time ?? null,
      rank(
        traced.map((t) => t.inputs),
        traced[i]?.inputs ?? 0,
      ),
      lines.some((l) => "to" in l && l.to === p.id),
    ]),
    queued: s.queued.map((q) => [q.machine, q.state, q.stale]),
  };
}

/**
 * Returns a fingerprint of the state after the last input: two runs with the same fingerprint reach the same state and
 * report the same violations on the same later inputs, apart from a violation that a run reports only once. The queue
 * and each instance's awaitingOnDone are left out: they are empty after an input that completed (see clone), and a
 * halted run takes no more inputs. The open shows subscriptions are the pending requests of shows slots that are not
 * stale. The counts of line ids and of created keys decide the ids and keys that later lines and records get. Also left
 * out are the records of what happened: the trace, violations, steps, messageCount, coverage and request pairs, and the
 * write counts of values, which only decide whether a cached evaluation is reused. The sets of violations already
 * reported are left out too: they only stop a run from reporting a violation twice. The outgoing requests are compared as a
 * set. The copies of a map state follow their owner, in the order of their keys; a closed copy that no map state lists
 * is left out, since the run reads from it only what its id names (owner, map and key) and that it is closed. The
 * deadlines stay in entry order, which is the order of the due deadlines.
 */
export function fingerprint(r: Processing): string {
  const s = r.state;
  return canonicalJson({
    now: s.now.toString(),
    lineCounts: [...s.lineCounts].toSorted(byKey),
    keyCounts: keyCounts(s).toSorted(byKey),
    records: [
      ...[...s.records.keyed].map(([name, rows]) => [
        name,
        [...rows].map(([key, row]): [string, unknown] => [key, row.encoded]).toSorted(byKey),
      ]),
      ...[...s.records.singles].map(([name, row]) => [name, row.encoded]),
    ],
    requests: requestsFingerprint(r),
    deadlines: s.deadlines.map((t) => [t.machine, t.state, t.name, t.time?.toString() ?? null]),
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
      .map(([id, { request, answer }]) => [id, request.name, JSON.stringify(request.input), answer]),
    deliveries: [...s.deliveries].toSorted(),
    outgoing: [...s.outgoing]
      .map(([id, { activity, answer, accepted }]) =>
        canonicalJson([
          id,
          activity.target,
          answer ?? null,
          accepted === undefined
            ? null
            : [accepted.input, accepted.output ?? null, accepted.events.map((e) => [e.event, e.payload])],
        ]),
      )
      .toSorted(),
    started: s.started,
  });
}
