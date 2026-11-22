import { join, relative } from "node:path";
import type { CheckedSpec } from "../check/spec.ts";
import { ask } from "../cli/engine.ts";
import type { DefinitionRef } from "../data/definitionRef.ts";
import { type FileLine, isMalformed, parseFileLines } from "../data/trace.ts";
import { type Run, readTrace, runFile, sameRun, snapshotPath } from "../data/traceFile.ts";
import { type ReportedViolation, zodError } from "../data/violation.ts";
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

/** A trace's lines as the engine reads them: null for a blank line, "malformed" for one the line schema rejects. */
const fileLines = (lines: readonly FileLine[]) =>
  lines.map((l) => (l === undefined ? null : isMalformed(l) ? ("malformed" as const) : l));

/** The findings with the line schema's issues on each Uncomparable.lineSchema, which the trace's parse found. */
const withLineErrors = (found: readonly Found[], lines: readonly FileLine[]): Found[] =>
  found.map((f) => {
    const line = f.line === undefined ? undefined : lines[f.line - 1];
    return f.kind === "Uncomparable.lineSchema" && line !== undefined && isMalformed(line)
      ? { ...f, error: zodError(line.issues) }
      : f;
  });

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
  const snapshots = pairing.compare.map((run) => ({ run, snapshot: readSnapshotViolations(snapshotPath(spec, run)) }));
  const compared = snapshots.filter(({ snapshot }) => snapshot.violations.length === 0);
  const traceOf = (path: string) => parseFileLines(readTrace(path));
  const compareTraces = compared.map(({ run }) => traceOf(join(folder, runFile(run))));
  const contractTraces = pairing.contract.map((t) => traceOf(join(folder, t.service, `${t.name}.jsonl`)));
  const verified = ask(
    "verifyTrace",
    compared.map(({ run, snapshot }, i) => ({
      structure: spec.structure,
      service: run.runner,
      snapshot: snapshot.lines.map((l) => l ?? null),
      trace: fileLines(compareTraces[i] ?? []),
    })),
  );
  const external = ask(
    "verifyExternal",
    pairing.contract.map((t, i) => ({
      structure: spec.structure,
      service: t.service,
      trace: fileLines(contractTraces[i] ?? []),
    })),
  );
  const comparedViolations = snapshots.flatMap(({ run, snapshot }) => {
    if (snapshot.violations.length > 0) return atLines(snapshotPath(spec, run), snapshot.violations, scenarioOf(run));
    const i = compared.findIndex((c) => c.run === run);
    return atLines(
      join(folder, runFile(run)),
      withLineErrors(verified[i]?.findings ?? [], compareTraces[i] ?? []),
      scenarioOf(run),
    );
  });
  const checked = pairing.contract.flatMap((t, i) =>
    atLines(
      join(folder, t.service, `${t.name}.jsonl`),
      withLineErrors(external[i]?.findings ?? [], contractTraces[i] ?? []),
    ),
  );
  const unpaired = pairing.violations.map((p) => tracePairingViolation(spec, p, folder));
  return {
    traces: pairing.compare.length + pairing.contract.length,
    violations: [...comparedViolations, ...checked, ...unpaired],
  };
}

/**
 * Returns every run that has a snapshot: each scenario's own run, and each run of another spec service in a scenario.
 * `drive` drives an implementation of the run's `runner` through it, and verify compares the trace at `runFile(run)` in
 * the trace folder with it.
 */
export const snapshotRuns = (spec: CheckedSpec): Run[] => withSnapshot(spec, allRuns(spec));
