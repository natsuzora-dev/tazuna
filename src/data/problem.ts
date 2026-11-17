import type { DefinitionRef } from "./definitionRef.ts";
import type { Line } from "./scenario.generated.ts";
import type { Location, Placed, ProblemError, ViolationValue } from "./violation.ts";

/**
 * A reported violation, with its location. `scenario` is the scenario that the violation is about, and `appendedLines`
 * the lines appended to it before the violation.
 */
export interface Problem extends ViolationValue {
  readonly location: Location;
  readonly scenario?: DefinitionRef;
  readonly appendedLines?: readonly Line[];
  readonly error?: ProblemError;
}

/**
 * Returns the violation as a Problem at `at`, with the scenario and the line that the violation names itself in its
 * place.
 */
export function toProblem(
  v: ViolationValue & Placed & Pick<Problem, "error">,
  at: Location,
  extra: Pick<Problem, "scenario" | "appendedLines"> = {},
): Problem {
  const line = v.line ?? at.line;
  const scenario = v.scenario ?? extra.scenario;
  return {
    kind: v.kind,
    definition: v.definition,
    data: v.data,
    location: { file: at.file, ...(line === undefined ? {} : { line }) },
    ...(scenario === undefined ? {} : { scenario }),
    ...(extra.appendedLines === undefined ? {} : { appendedLines: extra.appendedLines }),
    ...(v.error === undefined ? {} : { error: v.error }),
  };
}
