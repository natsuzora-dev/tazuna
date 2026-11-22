import { ask } from "../cli/engine.ts";
import type { DefinitionRef } from "../data/definitionRef.ts";
import type { TraceLine } from "../data/trace.generated.ts";
import type { MalformedLine } from "../data/trace.ts";
import { parseLines } from "../data/trace.ts";
import { readTrace } from "../data/traceFile.ts";
import type { Uncomparable } from "../data/uncomparable.generated.ts";
import type { Json } from "../data/values.ts";
import { type Placed, type ReportedViolation, toReported, type ViolationValue, zodError } from "../data/violation.ts";

export type Found = ViolationValue & Placed & Pick<ReportedViolation, "error">;

const lineSchema = ({ lineNumber, issues }: MalformedLine): Found => {
  const value: Uncomparable = { kind: "Uncomparable.lineSchema", definition: null, line: lineNumber, data: {} };
  return { ...value, error: zodError(issues) };
};

/**
 * Returns the JSON values and the lines of the snapshot file at `path`, undefined at blank lines, and its violations at
 * their snapshot lines: each line that the trace line schema cannot read, or, when every line is read, each unknown
 * after.
 */
export function readSnapshotViolations(path: string): {
  readonly values: readonly (Json | undefined)[];
  readonly lines: readonly (TraceLine | undefined)[];
  readonly violations: readonly Found[];
} {
  const values = readTrace(path);
  const { lines, malformed } = parseLines(values);
  if (malformed.length > 0) return { values, lines, violations: malformed.map(lineSchema) };
  const [afters] = ask("afters", [{ snapshot: lines.map((l) => l ?? null) }]);
  return { values, lines, violations: afters?.findings ?? [] };
}

/** Returns each violation as a ReportedViolation in `file`, at the line that it names, or at the whole file. */
export const violationsAt = (file: string, found: readonly Found[], scenario?: DefinitionRef): ReportedViolation[] =>
  found.map((v) => toReported(v, { file }, scenario === undefined ? {} : { scenario }));
