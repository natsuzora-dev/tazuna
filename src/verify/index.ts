import { join, relative } from "node:path";
import type { CheckedSpec } from "../check/spec.ts";
import { type DefinitionRef, sameRef } from "../data/definitionRef.ts";
import { parseFileLines } from "../data/trace.ts";
import { readTrace, snapshotPath } from "../data/traceFile.ts";
import type { ReportedViolation } from "../data/violation.ts";
import { compareTrace, verifying } from "./compare.ts";
import { verifyExternal } from "./external.ts";
import { type Found, readSnapshotViolations, violationsAt } from "./lines.ts";
import { pairingViolation, pairTraces, traceFolderOf } from "./pairing.ts";
import { hasSnapshot, type SnapshotRun, snapshotRuns } from "./snapshot.ts";

export { type CheckedSpec, checkSpec, type SpecCheck } from "../check/spec.ts";
export type { GivenRecord } from "../data/scenario.generated.ts";
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
} from "./adapter.ts";
export { drive, lineIds, type Run } from "./harness.ts";

/**
 * Compares the traces in `folder`, which `drive` wrote, with the snapshots without running the spec, and checks each
 * trace of an external service, <service>/<name>.jsonl with any name, against the service's contract. A scenario's
 * trace is <service>/<scenario>.jsonl. The trace of a running peer's run in a scenario, <service>/<scenario>.<peer>.jsonl
 * after its snapshot, records the peer's implementation and compares as the peer's.
 * Skips the traces of runs that have no snapshot, and reports each other entry of the folder and the snapshots that
 * have no trace. A trace line's violation is at its line. A violation of the snapshot, a line that the trace line
 * schema cannot read or an unknown after, is at the snapshot line, and then the trace is not compared.
 */
export function verifyTraces(spec: CheckedSpec, folder: string): { traces: number; violations: ReportedViolation[] } {
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
    violationsAt(relative(spec.root, path), found, scenario);
  const compared = pairing.compare.flatMap((t) => {
    const snapshot = readSnapshotViolations(snapshotPath(spec, t));
    if (snapshot.violations.length > 0) return atLines(snapshotPath(spec, t), snapshot.violations, t);
    return atLines(
      traceFile(t),
      compareTrace(spec, runnerOf(t), snapshot.lines, readTrace(traceFile(t)), verifying).found,
      t,
    );
  });
  const checked = pairing.contract.flatMap((t) =>
    atLines(traceFile(t), verifyExternal(spec, t.service, parseFileLines(readTrace(traceFile(t))))),
  );
  const unpaired = pairing.violations.map((p) => pairingViolation(spec, p, folder));
  return {
    traces: pairing.compare.length + pairing.contract.length,
    violations: [...compared, ...checked, ...unpaired],
  };
}

/**
 * Returns the snapshots of running peers' runs in scenarios. `drive` drives an implementation of a snapshot's `runner`
 * through it as through a scenario's snapshot, and verify compares the trace <service>/<name>.jsonl with it.
 */
export function peerSnapshots(spec: CheckedSpec): SnapshotRun[] {
  const runs = snapshotRuns(spec).filter((r) => r.runner !== r.service);
  return runs.filter(hasSnapshot(spec, runs));
}
