import type { DefinitionRef } from "./definitionRef.ts";
import type { Step } from "./step.generated.ts";
import type { Location, Placed, ProblemError, ViolationValue } from "./violation.ts";

/**
 * A reported violation, with its location. `scenario` is the scenario that the violation is about. `appendedInputs`
 * holds the inputs appended to the scenario before it.
 */
export interface Problem extends ViolationValue {
  readonly location: Location;
  readonly scenario?: DefinitionRef;
  readonly appendedInputs?: readonly Step[];
  readonly error?: ProblemError;
}

/**
 * Returns the violation as a Problem at `at`, with the scenario, the line, and the input that the violation names
 * itself in its place.
 */
export function toProblem(
  v: ViolationValue & Placed & Pick<Problem, "error">,
  at: Location,
  extra: Pick<Problem, "scenario" | "appendedInputs"> = {},
): Problem {
  const line = v.line ?? at.line;
  const input = v.input ?? at.input;
  const scenario = v.scenario ?? extra.scenario;
  return {
    kind: v.kind,
    definition: v.definition,
    data: v.data,
    location: { file: at.file, ...(line === undefined ? {} : { line }), ...(input === undefined ? {} : { input }) },
    ...(scenario === undefined ? {} : { scenario }),
    ...(extra.appendedInputs === undefined ? {} : { appendedInputs: extra.appendedInputs }),
    ...(v.error === undefined ? {} : { error: v.error }),
  };
}
