import { join, relative } from "node:path";
import { type DefinitionRef, sameRef } from "../data/definitionRef.ts";
import type { Problem } from "../data/problem.ts";
import { parseFileLines } from "../data/trace.ts";
import { readTrace, snapshotPath } from "../data/traceFile.ts";
import type { Spec } from "../load/load.ts";
import { compareTrace } from "./compare.ts";
import { verifyExternal } from "./external.ts";
import { type Found, problemsAt, readSnapshotProblems } from "./lines.ts";
import { pairingProblem, pairTraces, traceFolderOf } from "./pairing.ts";
import { hasSnapshot, type SnapshotRun, snapshotRuns } from "./snapshot.ts";

export type { GivenRecord } from "../data/scenario.generated.ts";
export { drive, lineIds, type Run } from "./harness.ts";
export {
  type Adapter,
  commandRequest,
  decodeAnswer,
  type ForeignRequest,
  type InputMessage,
  type OutputSlot,
  type Outputs,
  queryRequest,
  Unsettled,
} from "./ports.ts";

/**
 * Compares the traces in `folder`, which `drive` wrote, with the snapshots without running the spec, and checks each
 * trace of an external service, <service>/<name>.jsonl with any name, against the service's contract. A scenario's
 * trace is <service>/<scenario>.jsonl. The trace of a running peer's run in a scenario, <service>/<scenario>.<peer>.jsonl
 * after its snapshot, records the peer's implementation and compares as the peer's.
 * Skips the traces of runs that have no snapshot, and reports each other entry of the folder and the snapshots that
 * have no trace. A trace line's violation is at its line. A violation of the snapshot, a line that the trace line
 * schema cannot read or an unknown after, is at the snapshot line, and then the trace is not compared.
 */
export function verifyTraces(spec: Spec, folder: string): { traces: number; problems: Problem[] } {
  const runs = snapshotRuns(spec);
  const snapshotted = hasSnapshot(spec, runs);
  const pairing = pairTraces(
    spec.structure.services,
    runs.map(({ service, name }) => ({ service, name, compared: snapshotted({ service, name }) })),
    traceFolderOf(folder),
  );
  const runnerOf = (t: DefinitionRef) => (runs.find((r) => sameRef(r, t)) as SnapshotRun).runner;
  const traceFile = (t: DefinitionRef) => join(folder, t.service, `${t.name}.jsonl`);
  const atLines = (path: string, found: readonly Found[], scenario?: DefinitionRef) =>
    problemsAt(relative(spec.root, path), found, scenario);
  const compared = pairing.compare.flatMap((t) => {
    const snapshot = readSnapshotProblems(snapshotPath(spec, t));
    if (snapshot.problems.length > 0) return atLines(snapshotPath(spec, t), snapshot.problems, t);
    return atLines(traceFile(t), compareTrace(spec, runnerOf(t), snapshot.lines, readTrace(traceFile(t))).found, t);
  });
  const checked = pairing.contract.flatMap((t) =>
    atLines(traceFile(t), verifyExternal(spec, t.service, parseFileLines(readTrace(traceFile(t))))),
  );
  const unpaired = pairing.problems.map((p) => pairingProblem(spec, p, folder));
  return { traces: pairing.compare.length + pairing.contract.length, problems: [...compared, ...checked, ...unpaired] };
}

/**
 * Returns the snapshots of running peers' runs in scenarios. `drive` drives an implementation of a snapshot's `runner`
 * through it as through a scenario's snapshot, and verify compares the trace <service>/<name>.jsonl with it.
 */
export function peerSnapshots(spec: Spec): SnapshotRun[] {
  const runs = snapshotRuns(spec).filter((r) => r.runner !== r.service);
  return runs.filter(hasSnapshot(spec, runs));
}
