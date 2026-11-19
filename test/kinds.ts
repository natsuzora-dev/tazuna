import { type Kind, kindsOf } from "../src/data/kinds.ts";

const dslCovered = new Set<Kind>([
  "InvalidScenario.brokenGivenInvariant",
  "InvalidScenario.duplicateRecord",
  "InvalidScenario.leftInFlight",
  "InvalidScenario.unlistedPeer",
  "InvalidScenario.unmetExpectation",
]);

/** The kinds that no example reports, each with the reason. */
export const unexemplified: Readonly<Partial<Record<Kind, string>>> = {
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
  ...Object.fromEntries(
    kindsOf.InvalidScenario.filter((kind) => !dslCovered.has(kind)).map((kind) => [
      kind,
      "No DSL example under test/run/invalidScenario yet; a data scenario under test/sim exemplifies it",
    ]),
  ),
};
