import { join, relative } from "node:path";
import type { CheckedSpec } from "../check/spec.ts";
import type { DefinitionRef } from "../data/definitionRef.ts";
import { parseFileLines } from "../data/trace.ts";
import { type Run, readTrace, runFile, sameRun, snapshotPath } from "../data/traceFile.ts";
import type { ReportedViolation } from "../data/violation.ts";
import { compareTrace, verifying } from "./compare.ts";
import { verifyExternal } from "./external.ts";
import { type Found, readSnapshotViolations, violationsAt } from "./lines.ts";
import { pairTraces, scenarioOf, traceFolderOf, tracePairingViolation } from "./pairing.ts";
import { snapshotRuns as allRuns, withSnapshot } from "./snapshot.ts";

export { type CheckedSpec, checkSpec, failureText, type SpecCheck } from "../check/spec.ts";
export type { GivenRecord } from "../data/scenario.generated.ts";
export { type Run, runFile } from "../data/traceFile.ts";
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
export { drive, lineIds } from "./harness.ts";

/**
 * Compares the traces in `folder`, which `drive` wrote, with the snapshots without running the spec, and checks each
 * trace of an external service, <service>/<name>.jsonl with any name, against the service's contract. The trace of a
 * run is at runFile(run) and compares as the trace of the run's runner.
 * Skips the traces of runs that have no snapshot, and reports each other entry of the folder and the snapshots that
 * have no trace. A trace line's violation is at its line. A violation of the snapshot, a line that the trace line
 * schema cannot read or an unknown after, is at the snapshot line, and then the trace is not compared.
 */
export function verifyTraces(spec: CheckedSpec, folder: string): { traces: number; violations: ReportedViolation[] } {
  const runs = allRuns(spec);
  const snapshotted = withSnapshot(spec, runs);
  const pairing = pairTraces(
    spec.structure.services,
    runs.map((run) => ({ run, compared: snapshotted.some((s) => sameRun(s, run)) })),
    traceFolderOf(folder),
  );
  const atLines = (path: string, found: readonly Found[], scenario?: DefinitionRef) =>
    violationsAt(relative(spec.root, path), found, scenario);
  const compared = pairing.compare.flatMap((run) => {
    const trace = join(folder, runFile(run));
    const snapshot = readSnapshotViolations(snapshotPath(spec, run));
    if (snapshot.violations.length > 0) return atLines(snapshotPath(spec, run), snapshot.violations, scenarioOf(run));
    return atLines(
      trace,
      compareTrace(spec, run.runner, snapshot.lines, readTrace(trace), verifying).found,
      scenarioOf(run),
    );
  });
  const checked = pairing.contract.flatMap((t) => {
    const trace = join(folder, t.service, `${t.name}.jsonl`);
    return atLines(trace, verifyExternal(spec, t.service, parseFileLines(readTrace(trace))));
  });
  const unpaired = pairing.violations.map((p) => tracePairingViolation(spec, p, folder));
  return {
    traces: pairing.compare.length + pairing.contract.length,
    violations: [...compared, ...checked, ...unpaired],
  };
}

/**
 * Returns every run that has a snapshot: each scenario's own run, and each run of another spec service in a scenario.
 * `drive` drives an implementation of the run's `runner` through it, and verify compares the trace at `runFile(run)` in
 * the trace folder with it.
 */
export const snapshotRuns = (spec: CheckedSpec): Run[] => withSnapshot(spec, allRuns(spec));
