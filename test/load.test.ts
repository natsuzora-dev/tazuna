import type { Malformed } from "../src/data/malformed.ts";
import type { NonCanonical } from "../src/data/nonCanonical.ts";
import type { Restricted } from "../src/data/restricted.ts";
import { groupExamples } from "./examples.ts";
import { testEveryKind, testExamples } from "./expected.ts";

const groups = { malformed: "Malformed", nonCanonical: "NonCanonical", restricted: "Restricted" } as const;

for (const [folder, group] of Object.entries(groups))
  testExamples(groupExamples("load", folder), group, ["check", "."]);

const kinds: Readonly<Record<Malformed["kind"] | NonCanonical["kind"] | Restricted["kind"], true>> = {
  "Malformed.missingDefiner": true,
  "Malformed.unlistedEntity": true,
  "Malformed.listedTwice": true,
  "Malformed.listedUnderOtherName": true,
  "Malformed.serviceInSharedFolder": true,
  "Malformed.splitService": true,
  "Malformed.misnamedService": true,
  "Malformed.duplicateName": true,
  "Malformed.alias": true,
  "Malformed.opaqueCollection": true,
  "Malformed.defaultSchema": true,
  "Malformed.unexportedDefinition": true,
  "Malformed.unparsableTime": true,
  "Malformed.unknownPeer": true,
  "Malformed.inexactDelay": true,
  "Malformed.misnamedPeer": true,
  "Malformed.lineAfterWhen": true,
  "Malformed.misusedObserved": true,
  "NonCanonical.emptyGuard": true,
  "NonCanonical.emptyAfter": true,
  "NonCanonical.missingReenter": true,
  "NonCanonical.reenterOnRoot": true,
  "NonCanonical.reenterOutsideSource": true,
  "NonCanonical.ungroupedConstant": true,
  "NonCanonical.statelessMachine": true,
  "NonCanonical.missingOnRejected": true,
  "NonCanonical.unreachableOnRejected": true,
  "NonCanonical.unreadBinding": true,
  "NonCanonical.undescribedService": true,
  "NonCanonical.undescribedDefinition": true,
  "Restricted.global": true,
  "Restricted.member": true,
  "Restricted.alias": true,
  "Restricted.localeMethod": true,
  "Restricted.mutableModule": true,
  "Restricted.cryptoImport": true,
  "Restricted.nonNull": true,
  "Restricted.as": true,
  "Restricted.suppression": true,
  "Restricted.crossServiceImport": true,
};

testEveryKind(groupExamples("load"), Object.keys(kinds));
