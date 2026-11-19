import { groupExamples } from "./examples.ts";
import { testEveryKind, testExamples } from "./expected.ts";
import { loadKinds } from "./kinds.ts";

const groups = { malformed: "Malformed", nonCanonical: "NonCanonical", restricted: "Restricted" } as const;

for (const [folder, group] of Object.entries(groups))
  testExamples(groupExamples("load", folder), group, ["check", "."]);

testEveryKind(groupExamples("load"), Object.keys(loadKinds));
