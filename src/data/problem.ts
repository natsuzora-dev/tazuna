import type { DefinitionRef } from "./definitionRef.ts";
import type { Step } from "./step.generated.ts";
import type { Kind, Location, ProblemError, ViolationValue } from "./violation.ts";

/** A reported violation, with its location. `appendedInputs` holds the inputs appended to the scenario before it. */
export interface Problem extends ViolationValue {
  readonly location: Location;
  readonly scenario?: DefinitionRef;
  readonly appendedInputs?: readonly Step[];
  readonly error?: ProblemError;
}

export function toProblem(kind: Kind, v: Omit<Problem, "kind">): Problem {
  const { file, line } = v.location;
  return {
    kind,
    definition: v.definition,
    data: v.data,
    location: line === undefined ? { file } : { file, line },
    ...(v.scenario === undefined ? {} : { scenario: v.scenario }),
    ...(v.appendedInputs === undefined ? {} : { appendedInputs: v.appendedInputs }),
    ...(v.error === undefined ? {} : { error: v.error }),
  };
}
