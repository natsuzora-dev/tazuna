import { bagOrderDependentKinds } from "./bagOrderDependent.generated.ts";
import { choiceDependentKinds } from "./choiceDependent.generated.ts";
import { faultKinds } from "./fault.generated.ts";
import { illegalKinds } from "./illegal.generated.ts";
import { internalInvalidInputKinds, invalidInputKinds } from "./invalidInput.generated.ts";
import { internalInvalidScenarioKinds, invalidScenarioKinds } from "./invalidScenario.generated.ts";
import type { Malformed } from "./malformed.ts";
import { mismatchKinds } from "./mismatch.generated.ts";
import { nonCanonicalKinds as structureNonCanonicalKinds } from "./nonCanonical.generated.ts";
import type { SourceNonCanonical } from "./nonCanonical.ts";
import type { Restricted } from "./restricted.ts";
import { uncomparableKinds } from "./uncomparable.generated.ts";
import type { Uncovered } from "./uncovered.ts";
import { undecidedKinds } from "./undecided.generated.ts";
import type { Group } from "./violation.ts";

/** `list` when it holds every member of `U`; a missing member is a type error that names it. */
const every =
  <U extends string>() =>
  <const L extends readonly U[]>(
    list: L & ([Exclude<U, L[number]>] extends [never] ? unknown : Exclude<U, L[number]>),
  ) =>
    list;

const malformedKinds = every<Malformed["kind"]>()([
  "Malformed.unlistedFile",
  "Malformed.missingDefiner",
  "Malformed.unlistedEntity",
  "Malformed.listedTwice",
  "Malformed.listedUnderOtherName",
  "Malformed.duplicateService",
  "Malformed.unknownService",
  "Malformed.reservedNameCharacter",
  "Malformed.writtenCreatedKey",
  "Malformed.caseCollision",
  "Malformed.duplicateName",
  "Malformed.alias",
  "Malformed.opaqueCollection",
  "Malformed.unrepresentableSchema",
  "Malformed.misplacedSelfRef",
  "Malformed.defaultSchema",
  "Malformed.unexportedDefinition",
  "Malformed.unresolvedReference",
  "Malformed.unreadableDeadline",
  "Malformed.unparsableTime",
  "Malformed.unknownPeer",
  "Malformed.lineAfterWhen",
  "Malformed.misusedObserved",
]);

const nonCanonicalKinds = [
  ...structureNonCanonicalKinds,
  ...every<SourceNonCanonical["kind"]>()([
    "NonCanonical.emptyKeyword",
    "NonCanonical.ungroupedConstant",
    "NonCanonical.constantOffer",
    "NonCanonical.answerLiteral",
    "NonCanonical.unreadBinding",
    "NonCanonical.undescribedService",
    "NonCanonical.undescribedDefinition",
  ]),
] as const;

const restrictedKinds = every<Restricted["kind"]>()([
  "Restricted.global",
  "Restricted.member",
  "Restricted.alias",
  "Restricted.localeMethod",
  "Restricted.mutableModule",
  "Restricted.cryptoImport",
  "Restricted.nonNull",
  "Restricted.as",
  "Restricted.any",
  "Restricted.suppression",
  "Restricted.crossServiceImport",
]);

const uncoveredKinds = every<Uncovered["kind"]>()([
  "Uncovered.request",
  "Uncovered.successAnswer",
  "Uncovered.bindsRejection",
  "Uncovered.requiresRejection",
  "Uncovered.automation",
  "Uncovered.automationBindingValue",
  "Uncovered.automationBindingNull",
  "Uncovered.automationGuard",
  "Uncovered.transition",
  "Uncovered.guardFalse",
  "Uncovered.state",
]);

/** The kinds of each group. */
export const kindsOf = {
  Malformed: malformedKinds,
  NonCanonical: nonCanonicalKinds,
  Restricted: restrictedKinds,
  Illegal: illegalKinds,
  InvalidScenario: invalidScenarioKinds,
  InvalidInput: invalidInputKinds,
  Fault: faultKinds,
  BagOrderDependent: bagOrderDependentKinds,
  ChoiceDependent: choiceDependentKinds,
  Undecided: undecidedKinds,
  Uncovered: uncoveredKinds,
  Mismatch: mismatchKinds,
  Uncomparable: uncomparableKinds,
} as const satisfies { readonly [G in Group]: readonly `${G}.${string}`[] };

/** A violation kind. */
export type Kind = (typeof kindsOf)[Group][number];

/** Every group. */
export const groupNames = every<Group>()([
  "Malformed",
  "NonCanonical",
  "Restricted",
  "Illegal",
  "InvalidScenario",
  "InvalidInput",
  "Fault",
  "BagOrderDependent",
  "ChoiceDependent",
  "Undecided",
  "Uncovered",
  "Mismatch",
  "Uncomparable",
]);

const parsed: ReadonlyMap<string, { readonly kind: Kind; readonly group: Group }> = new Map(
  groupNames.flatMap((group) => kindsOf[group].map((kind: Kind) => [kind, { kind, group }] as const)),
);

/** Every violation kind. */
export const kinds: readonly Kind[] = [...parsed.values()].map((p) => p.kind);

/** The kinds that no spec that `tazuna check` passes can produce (Lean's `internal`). Explain leaves them out. */
export const internalKinds = [
  ...internalInvalidScenarioKinds,
  ...internalInvalidInputKinds,
] as const satisfies readonly Kind[];

/** A kind that a user meets: one of the kinds except internalKinds. */
export type UserKind = Exclude<Kind, (typeof internalKinds)[number]>;

const internal: ReadonlySet<Kind> = new Set(internalKinds);

/** Whether `kind` is a kind that a user meets. */
export const isUserKind = (kind: Kind): kind is UserKind => !internal.has(kind);

/** The kind that `text` names and its group, or undefined when `text` is no violation kind. */
export const parseKind = (text: string): { readonly kind: Kind; readonly group: Group } | undefined => parsed.get(text);
