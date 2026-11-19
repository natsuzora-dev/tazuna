import { kindsOf } from "../src/data/kinds.ts";
import { groupExamples } from "./examples.ts";
import { testEveryKind, testExamples } from "./expected.ts";

const groups = { malformed: "Malformed", nonCanonical: "NonCanonical", restricted: "Restricted" } as const;

for (const [folder, group] of Object.entries(groups))
  testExamples(groupExamples("load", folder), group, ["check", "."]);

testEveryKind(groupExamples("load"), [...kindsOf.Malformed, ...kindsOf.NonCanonical, ...kindsOf.Restricted]);
