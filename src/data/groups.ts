import type { Group } from "./violation.ts";

/** Who meets a violation of a group: the commands that report it, and the side at fault, which fixes it. */
export interface GroupInfo {
  readonly reportedBy: readonly ("check" | "test" | "test --coverage" | "verify")[];
  readonly fixedIn: string;
}

export const groups = {
  Malformed: { reportedBy: ["check"], fixedIn: "The spec." },
  NonCanonical: { reportedBy: ["check"], fixedIn: "The spec." },
  Restricted: { reportedBy: ["check"], fixedIn: "The spec." },
  Illegal: { reportedBy: ["check"], fixedIn: "The spec." },
  InvalidScenario: {
    reportedBy: ["test"],
    fixedIn:
      "The scenario: a line that cannot take place, a message that it leaves unstated, or an expectation of Then that does not hold or cannot fail.",
  },
  InvalidInput: {
    reportedBy: ["test"],
    fixedIn:
      "The scenario: a message that no sender could give the running service, including an external peer's answer that breaks the peer's contract.",
  },
  Fault: { reportedBy: ["test"], fixedIn: "The spec." },
  BagOrderDependent: { reportedBy: ["test"], fixedIn: "The spec." },
  ChoiceDependent: { reportedBy: ["test"], fixedIn: "The spec." },
  Undecided: {
    reportedBy: ["test"],
    fixedIn:
      "Neither side: the check stopped at a limit of tazuna. A smaller processing, or fewer created keys that only their keys tell apart, lets it decide.",
  },
  Uncovered: { reportedBy: ["test --coverage"], fixedIn: "The scenarios." },
  Mismatch: {
    reportedBy: ["test", "verify"],
    fixedIn:
      "The implementation or external service whose trace differs, or, for `test`, the snapshot that differs from its scenario's simulation.",
  },
  Uncomparable: {
    reportedBy: ["test", "verify"],
    fixedIn:
      "The trace whose `in` lines differ from the snapshot's or that pairs with it in more than one way, or, for `test`, a snapshot without a scenario or a scenario without a snapshot.",
  },
} as const satisfies Readonly<Record<Group, GroupInfo>>;
