import { join, relative } from "node:path";
import type { CheckedSpec } from "../check/spec.ts";
import { ask } from "../cli/engine.ts";
import type { Log } from "../cli/protocol.generated.ts";
import { entriesOf } from "../data/pairing.ts";
import { type FileLine, isMalformed, parseFileLines } from "../data/trace.ts";
import { readTrace } from "../data/traceFile.ts";
import type { Json } from "../data/values.ts";
import { type ReportedViolation, toReported, type ViolationValue, zodError } from "../data/violation.ts";
import { placeOf } from "../load/found.ts";
import { type Found, violationsAt } from "./lines.ts";

export { type CheckedSpec, checkSpec, failureText, type SpecCheck } from "../check/spec.ts";
export type { GivenRecord } from "../data/scenario.generated.ts";
export { type InputRun, type Run, runFile } from "../data/traceFile.ts";
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
export { drive, type LogLine, lineIds } from "./harness.ts";
export { inputRuns, snapshotRuns } from "./snapshot.ts";

/** A log's lines as the engine reads them: null for a blank line, "malformed" for one the line schema rejects. */
const fileLines = (lines: readonly FileLine[]) =>
  lines.map((l) => (l === undefined ? null : isMalformed(l) ? ("malformed" as const) : l));

/** The findings with the line schema's issues on each Uncomparable.lineSchema, which the log's parse found. */
const withLineErrors = (found: readonly Found[], lines: readonly FileLine[]): Found[] =>
  found.map((f) => {
    const line = f.line === undefined ? undefined : lines[f.line - 1];
    return f.kind === "Uncomparable.lineSchema" && line !== undefined && isMalformed(line)
      ? { ...f, error: zodError(line.issues) }
      : f;
  });

const isStartLine = (value: Json | undefined): boolean =>
  typeof value === "object" &&
  value !== null &&
  !Array.isArray(value) &&
  (value as Record<string, Json>)["type"] === "start";

/**
 * The log of a spec service's implementation in the file at `path`: its first line that is not blank is its start line
 * when its type is "start", which stays blank among the trace lines.
 */
export function readLog(service: string, path: string): { readonly log: Log; readonly lines: readonly FileLine[] } {
  const values = readTrace(path);
  const first = values.findIndex((v) => v !== undefined);
  const startValue = first === -1 ? undefined : values[first];
  const start = isStartLine(startValue) ? { line: first + 1, value: startValue as Json } : undefined;
  const lines = parseFileLines(start === undefined ? values : values.map((v, i) => (i === first ? undefined : v)));
  return { log: { service, ...(start === undefined ? {} : { start }), lines: fileLines(lines) }, lines };
}

/** The files under `folder`, at any depth, in name order, and the entries that are neither files nor folders. */
function filesUnder(folder: string): { readonly files: string[]; readonly others: string[] } {
  const files: string[] = [];
  const others: string[] = [];
  for (const e of entriesOf(folder)) {
    const path = join(folder, e.name);
    if (e.kind === "file") files.push(path);
    else if (e.kind === "folder") {
      const under = filesUnder(path);
      files.push(...under.files);
      others.push(...under.others);
    } else others.push(path);
  }
  return { files, others };
}

/**
 * Verifies the logs in `folder`. Each file under the folder <service> of a service of the spec, at any depth and with
 * any name, is a log of that service's implementation. The engine replays a spec service's log: the spec takes the
 * log's `in` lines and its lines are compared with the log's. An external service's log is checked against its
 * contract. Any other entry of the folder is a violation. `uncovered` holds the parts of the spec that no log reached.
 */
export function verifyTraces(
  spec: CheckedSpec,
  folder: string,
): { traces: number; violations: ReportedViolation[]; uncovered: readonly ViolationValue[] } {
  const at = (path: string) => relative(spec.root, path);
  const services = spec.structure.services;
  const unplaced: ReportedViolation[] = [];
  const logs: { service: string; path: string; external: boolean }[] = [];
  for (const e of entriesOf(folder)) {
    const path = join(folder, e.name);
    const service = services.find((s) => s.name === e.name);
    if (e.kind !== "folder")
      unplaced.push(
        toReported({ kind: "Uncomparable.unknownTraceEntry", definition: null, data: {} }, { file: at(path) }),
      );
    else if (service === undefined)
      unplaced.push(
        toReported(
          { kind: "Uncomparable.unknownService", definition: null, data: { service: e.name } },
          { file: at(path) },
        ),
      );
    else {
      const { files, others } = filesUnder(path);
      for (const file of files) logs.push({ service: service.name, path: file, external: service.external });
      for (const other of others)
        unplaced.push(
          toReported({ kind: "Uncomparable.unknownTraceEntry", definition: null, data: {} }, { file: at(other) }),
        );
    }
  }
  const replayed = logs.filter((l) => !l.external).map((l) => ({ ...l, ...readLog(l.service, l.path) }));
  const [verified] = ask("verify", [{ structure: spec.structure, logs: replayed.map((r) => r.log) }]);
  const ofReplays = replayed.flatMap((r, i) => {
    const result = verified?.logs[i];
    const file = at(r.path);
    return [
      ...violationsAt(file, withLineErrors(result?.findings ?? [], r.lines)),
      ...(result?.violations ?? []).map((v) =>
        toReported(v, v.definition === null ? { file } : placeOf(spec, v.definition)),
      ),
    ];
  });
  const contracts = logs.filter((l) => l.external).map((l) => ({ ...l, lines: parseFileLines(readTrace(l.path)) }));
  const external = ask(
    "verifyExternal",
    contracts.map((c) => ({ structure: spec.structure, service: c.service, trace: fileLines(c.lines) })),
  );
  const ofContracts = contracts.flatMap((c, i) =>
    violationsAt(at(c.path), withLineErrors(external[i]?.findings ?? [], c.lines)),
  );
  return {
    traces: logs.length,
    violations: [...ofReplays, ...ofContracts, ...unplaced],
    uncovered: verified?.uncovered ?? [],
  };
}
