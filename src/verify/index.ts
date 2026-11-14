import { join, relative } from "node:path";
import type { z } from "zod";
import type { CommandAnswer, QueryAnswer } from "../data/answer.ts";
import { type DefinitionRef, sameRef } from "../data/definitionRef.ts";
import type { Problem } from "../data/problem.ts";
import type { Answer, TraceLine } from "../data/trace.generated.ts";
import { parseFileLines } from "../data/trace.ts";
import { parseSnapshotFile, readTrace, snapshotPath } from "../data/traceFile.ts";
import { objectOf, type Shape } from "../data/values.ts";
import type { AnyCommand, AnyQuery } from "../dsl/definition.ts";
import type { Spec } from "../load/load.ts";
import { verifyExternal } from "./external.ts";
import { type Found, problemsAt, readSnapshotProblems } from "./lines.ts";
import { pairingProblem, pairTraces, traceFolderOf } from "./pairing.ts";
import { compareTrace } from "./prepare.ts";
import { hasSnapshot, type SnapshotRun, snapshotRuns } from "./snapshot.ts";

export { traceName } from "../load/traceName.ts";
export { matchRequest, rename } from "./replay.ts";

/**
 * Decodes the output of a fulfilled answer, or of an accepted answer of a command with output, with the definition's
 * output schema, and returns other answers as they are. Throws when the request has no answer with that result.
 */
export function decodeAnswer<Q extends AnyQuery>(
  query: Q,
  answer: Answer,
): QueryAnswer<z.output<z.ZodObject<Q["output"]>>>;

export function decodeAnswer<C extends AnyCommand>(
  command: C,
  answer: Answer,
): CommandAnswer<C["output"] extends Shape ? z.output<z.ZodObject<C["output"]>> : undefined>;

export function decodeAnswer(request: AnyCommand | AnyQuery, answer: Answer): Answer {
  if (answer.result === "rejected") return answer;
  if (answer.result !== (request.kind === "query" ? "fulfilled" : "accepted"))
    throw new Error(`a ${request.kind} has no ${answer.result} answer`);
  return request.output === undefined ? answer : { ...answer, output: objectOf(request.output).parse(answer.output) };
}

/**
 * Compares the traces in `folder` with the snapshots without running the spec, and checks each trace of an external
 * service, <service>/<name>.jsonl with any name, against the service's contract. A scenario's trace is
 * <service>/<scenario>.jsonl. The trace of another spec service's run on the inputs that test derives from a scenario,
 * <service>/<scenario>.<peer>.jsonl after its snapshot, records the peer's implementation and compares as the peer's.
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
 * Returns the snapshots of other spec services' runs on the inputs that test derives from scenarios. An implementation
 * of a snapshot's `runner` replays it as it replays a scenario's snapshot, and verify compares the trace
 * <service>/<name>.jsonl with it.
 */
export function peerSnapshots(spec: Spec): SnapshotRun[] {
  const runs = snapshotRuns(spec).filter((r) => r.runner !== r.service);
  return runs.filter(hasSnapshot(spec, runs));
}

/**
 * Reads the lines of a scenario's snapshot, or of a snapshot that peerSnapshots returns. Throws when the snapshot is
 * missing or has a line that is not a trace line.
 */
export function readSnapshot(spec: Spec, snapshot: DefinitionRef): TraceLine[] {
  const path = snapshotPath(spec, snapshot);
  const { lines, malformed } = parseSnapshotFile(path);
  if (malformed.length > 0)
    throw new Error(
      malformed.map((m) => `${path}:${m.lineNumber}: the line does not match the trace line schema`).join("\n"),
      { cause: malformed },
    );
  return lines;
}
