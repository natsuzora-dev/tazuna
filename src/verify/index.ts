import { join, relative } from "node:path";
import type { z } from "zod";
import type { CommandAnswer, QueryAnswer } from "../data/answer.ts";
import type { DefinitionRef } from "../data/definitionRef.ts";
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
import { hasSnapshot } from "./snapshot.ts";

export { alike } from "../data/canonical.ts";
export { traceName } from "../load/traceName.ts";

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
 * Compares the traces in `folder`, <service>/<scenario>.jsonl, with the snapshots without running the spec, and checks
 * each trace of an external service, <service>/<name>.jsonl with any name, against the service's contract. Skips the
 * traces of scenarios that have no snapshot, and reports each other entry of the folder and the snapshots that have no
 * trace. A trace line's violation is at its line. A violation of the snapshot, a line that the trace line schema cannot
 * read or an unknown after, is at the snapshot line, and then the trace is not compared.
 */
export function verifyTraces(spec: Spec, folder: string): { traces: number; problems: Problem[] } {
  const snapshotted = hasSnapshot(spec);
  const pairing = pairTraces(
    spec.structure.services,
    spec.scenarios.map(({ service, name }) => ({ service, name, compared: snapshotted({ service, name }) })),
    traceFolderOf(folder),
  );
  const traceFile = (t: DefinitionRef) => join(folder, t.service, `${t.name}.jsonl`);
  const atLines = (path: string, found: readonly Found[]) => problemsAt(relative(spec.root, path), found);
  const compared = pairing.compare.flatMap((t) => {
    const snapshot = readSnapshotProblems(snapshotPath(spec, t));
    if (snapshot.problems.length > 0) return atLines(snapshotPath(spec, t), snapshot.problems);
    return atLines(traceFile(t), compareTrace(spec, t.service, snapshot.lines, readTrace(traceFile(t))).found);
  });
  const checked = pairing.contract.flatMap((t) =>
    atLines(traceFile(t), verifyExternal(spec, t.service, parseFileLines(readTrace(traceFile(t))))),
  );
  const unpaired = pairing.problems.map((p) => pairingProblem(spec, p, folder));
  return { traces: pairing.compare.length + pairing.contract.length, problems: [...compared, ...checked, ...unpaired] };
}

/**
 * Reads the lines of a scenario's snapshot. Throws when the snapshot is missing or has a line that is not a trace line.
 */
export function readSnapshot(spec: Spec, scenario: DefinitionRef): TraceLine[] {
  const path = snapshotPath(spec, scenario);
  const { lines, malformed } = parseSnapshotFile(path);
  if (malformed.length > 0)
    throw new Error(
      malformed.map((m) => `${path}:${m.lineNumber}: the line does not match the trace line schema`).join("\n"),
      { cause: malformed },
    );
  return lines;
}
