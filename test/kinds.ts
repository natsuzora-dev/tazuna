import { bagOrderDependentKinds } from "../src/data/bagOrderDependent.generated.ts";
import { choiceDependentKinds } from "../src/data/choiceDependent.generated.ts";
import { faultKinds } from "../src/data/fault.generated.ts";
import { illegalKinds } from "../src/data/illegal.generated.ts";
import { invalidInputKinds } from "../src/data/invalidInput.generated.ts";
import { invalidScenarioKinds } from "../src/data/invalidScenario.generated.ts";
import type { Malformed } from "../src/data/malformed.ts";
import { mismatchKinds } from "../src/data/mismatch.generated.ts";
import type { NonCanonical } from "../src/data/nonCanonical.ts";
import type { Restricted } from "../src/data/restricted.ts";
import { uncomparableKinds } from "../src/data/uncomparable.generated.ts";
import type { Uncovered } from "../src/data/uncovered.ts";

/** The kinds that loading finds, which only TS defines. */
export const loadKinds: Readonly<Record<Malformed["kind"] | NonCanonical["kind"] | Restricted["kind"], true>> = {
  "Malformed.unlistedFile": true,
  "Malformed.missingDefiner": true,
  "Malformed.unlistedEntity": true,
  "Malformed.listedTwice": true,
  "Malformed.listedUnderOtherName": true,
  "Malformed.duplicateService": true,
  "Malformed.unknownService": true,
  "Malformed.reservedNameCharacter": true,
  "Malformed.writtenCreatedKey": true,
  "Malformed.caseCollision": true,
  "Malformed.duplicateName": true,
  "Malformed.alias": true,
  "Malformed.opaqueCollection": true,
  "Malformed.unrepresentableSchema": true,
  "Malformed.misplacedSelfRef": true,
  "Malformed.defaultSchema": true,
  "Malformed.unexportedDefinition": true,
  "Malformed.unparsableTime": true,
  "Malformed.unknownPeer": true,
  "Malformed.inexactDelay": true,
  "Malformed.lineAfterWhen": true,
  "Malformed.misusedObserved": true,
  "NonCanonical.emptyKeyword": true,
  "NonCanonical.missingReenter": true,
  "NonCanonical.reenterOnRoot": true,
  "NonCanonical.reenterOutsideSource": true,
  "NonCanonical.ungroupedConstant": true,
  "NonCanonical.statelessMachine": true,
  "NonCanonical.missingOnRejected": true,
  "NonCanonical.unreachableOnRejected": true,
  "NonCanonical.constantOffer": true,
  "NonCanonical.answerLiteral": true,
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

export const uncoveredKinds: Readonly<Record<Uncovered["kind"], true>> = {
  "Uncovered.request": true,
  "Uncovered.successAnswer": true,
  "Uncovered.bindsRejection": true,
  "Uncovered.requiresRejection": true,
  "Uncovered.automation": true,
  "Uncovered.automationBindingValue": true,
  "Uncovered.automationBindingNull": true,
  "Uncovered.automationGuard": true,
  "Uncovered.transition": true,
  "Uncovered.guardFalse": true,
  "Uncovered.state": true,
};

export const allKinds: readonly string[] = [
  ...Object.keys(loadKinds),
  ...illegalKinds,
  ...invalidScenarioKinds,
  ...invalidInputKinds,
  ...faultKinds,
  ...bagOrderDependentKinds,
  ...choiceDependentKinds,
  ...mismatchKinds,
  ...uncomparableKinds,
  ...Object.keys(uncoveredKinds),
];

/** The kinds that no example reports, each with the reason. */
export const unexemplified: Readonly<Record<string, string>> = {
  "InvalidInput.unownedTarget":
    "Only a data scenario names a target that its receiver does not own (the DSL's types let the client send only the definitions of the service it names); test/sim/Run/network/unownedTarget exemplifies it",
  "InvalidInput.unlistedRejectionReason":
    "The type of an answer accepts as the reason of a requires rejection only a requires condition of the request",
  "InvalidInput.unknownControl":
    "The type of operate accepts only the controls of the screen, and the exploration of test operates only those",
  "InvalidInput.unreadyStep":
    "Only test's step-order search writes a step order, naming only the steps that an execution took",
  "InvalidInput.unusedStepOrder":
    "Only test's step-order search writes a step order, naming only the steps that an execution took",
  "ChoiceDependent.uncomparable":
    "verify binds each created key at its first place in the outputs, so the records compare under bindings that fix every created key, unless the outputs cannot be compared with themselves; an example needs equal requests with different answers and seven created records that only their keys tell apart",
  "Fault.exceededMessageWork":
    "An example that reaches the limit 100000 writes about 8300 event lines in one message and makes run.diff several times slower",
  "Fault.exceededExitDepth": "Reaching the exit nesting limit 100 takes about 50 nested screen definitions",
  "Malformed.unlistedFile": "the examples skip tsc; cli.test.ts runs tsc on a spec that its tsconfig leaves out",
};
