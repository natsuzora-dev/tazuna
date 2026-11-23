import type { Group } from "./kinds.ts";

/** Who meets a violation of a group: the commands that report it, and the side at fault, which fixes it. */
export interface GroupInfo {
  readonly reportedBy: readonly ("check" | "test" | "verify" | "verify --coverage" | "prove")[];
  readonly fixedIn: string;
}

export const groups = {
  Malformed: { reportedBy: ["check"], fixedIn: "The spec." },
  NonCanonical: { reportedBy: ["check"], fixedIn: "The spec." },
  Restricted: { reportedBy: ["check"], fixedIn: "The spec." },
  Illegal: { reportedBy: ["check"], fixedIn: "The spec." },
  InvalidScenario: {
    reportedBy: ["test", "verify"],
    fixedIn:
      "The scenario: a line that cannot take place, a message that it leaves unstated, or an expectation of Then that does not hold or cannot fail. For `verify`, the start line of the trace, whose records the spec rejects.",
  },
  InvalidInput: {
    reportedBy: ["test", "verify"],
    fixedIn:
      "The scenario, or for `verify` the trace: a message that no sender could give the running service, including an external peer's answer that breaks the peer's contract.",
  },
  Fault: { reportedBy: ["test", "verify", "prove"], fixedIn: "The spec." },
  RegionOrderDependent: { reportedBy: ["test", "verify"], fixedIn: "The spec." },
  ChoiceDependent: { reportedBy: ["prove"], fixedIn: "The spec." },
  Uncovered: { reportedBy: ["verify --coverage"], fixedIn: "The tests that write the traces." },
  Mismatch: {
    reportedBy: ["test", "verify"],
    fixedIn:
      "The implementation or external service whose trace differs, or, for `test`, the snapshot that differs from its scenario's simulation.",
  },
  Uncomparable: {
    reportedBy: ["test", "verify"],
    fixedIn:
      "The trace that the spec cannot replay or compare in one way, or an entry of the traces folder that is no trace, or, for `test`, a snapshot without a scenario or a scenario without a snapshot.",
  },
} as const satisfies Readonly<Record<Group, GroupInfo>>;
