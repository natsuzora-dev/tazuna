import { join, relative, sep } from "node:path";
import type { Illegal } from "../data/illegal.generated.ts";
import { InternalError } from "../data/internalError.ts";
import type { Malformed } from "../data/malformed.ts";
import type { NonCanonical } from "../data/nonCanonical.ts";
import type { Restricted } from "../data/restricted.ts";
import type { ReportedViolation } from "../data/violation.ts";
import type { Place } from "../dsl/definition.ts";
import { comparePlaces, type Found, placeOf, reportedOfFound } from "../load/found.ts";
import { type LoadedSpec, loadSpec, type Spec } from "../load/load.ts";
import { check as validate } from "../validation/check.ts";
import * as answers from "./nonCanonical/answers.ts";
import * as binds from "./nonCanonical/binds.ts";
import * as charts from "./nonCanonical/charts.ts";
import * as constants from "./nonCanonical/constants.ts";
import * as descriptions from "./nonCanonical/descriptions.ts";
import * as keywords from "./nonCanonical/keywords.ts";
import * as offers from "./nonCanonical/offers.ts";
import * as rejections from "./nonCanonical/rejections.ts";
import * as sources from "./restricted/sources.ts";
import { type TypeCheck, typeCheck } from "./typeCheck.ts";

declare const checked: unique symbol;

/** A spec in which checkSpec found no violation. Only checkSpec makes one. */
export type CheckedSpec = Spec & { readonly [checked]: true };

/** Why checkSpec returned no checked spec. All but `typeErrors` and `violations` are usage errors. */
export type SpecFailure =
  | { readonly kind: "noTsconfig" }
  | { readonly kind: "noTypescript" }
  | { readonly kind: "unfinished"; readonly reason: string }
  | { readonly kind: "unloadable"; readonly reason: string }
  | { readonly kind: "typeErrors"; readonly output: string }
  | { readonly kind: "violations"; readonly files: number; readonly violations: readonly ReportedViolation[] };

export type SpecCheck = SpecFailure | { readonly kind: "checked"; readonly spec: CheckedSpec };

const syntaxChecks: readonly { readonly check: (spec: LoadedSpec) => readonly Found<NonCanonical | Restricted>[] }[] = [
  answers,
  binds,
  constants,
  descriptions,
  keywords,
  offers,
  sources,
];

/** The syntax checks that read the structure, which they skip on a spec without one. */
const structureChecks: readonly { readonly check: (spec: Spec) => readonly Found<NonCanonical>[] }[] = [
  charts,
  rejections,
];

function placeOfIllegal(spec: LoadedSpec, illegal: Illegal): Place {
  switch (illegal.kind) {
    case "Illegal.foreignMember": {
      const contract = spec.contracts.find((c) => c.service === illegal.data.contract);
      if (contract === undefined) throw new InternalError(`no contract of ${illegal.data.contract}`);
      return contract.place;
    }
    case "Illegal.automationCycle":
    case "Illegal.missingParent":
    case "Illegal.ownQuery":
    case "Illegal.unlistedControl":
    case "Illegal.alwaysCycle":
    case "Illegal.foreignEvent":
    case "Illegal.indexReason":
    case "Illegal.restoredHeld":
    case "Illegal.inexactDelay":
      return placeOf(spec, illegal.definition);
  }
}

/** Returns the header lines of Node's error and the first stack frame outside node: internals. */
function reason(error: unknown): string {
  if (!(error instanceof Error)) return String(error);
  const lines = (error.stack ?? error.message).split("\n");
  const frames = lines.findIndex((line) => line.startsWith("    at "));
  if (frames === -1) return lines.join("\n");
  const own = lines.slice(frames).find((line) => !line.includes("(node:") && !line.includes(" node:"));
  return [...lines.slice(0, frames), ...(own === undefined ? [] : [own])].join("\n");
}

/** Returns the text of `failure`, naming the spec folder `folder`; a violation is one JSON line. */
export function failureText(failure: SpecFailure, folder: string): string {
  switch (failure.kind) {
    case "noTsconfig":
      return `no tsconfig.json at or above ${folder}`;
    case "noTypescript":
      return `cannot resolve typescript from ${folder}`;
    case "unfinished":
      return `tsc did not finish: ${failure.reason}`;
    case "unloadable":
      return `cannot load ${folder}: ${failure.reason.replace(/\s+/g, " ").trim()}`;
    case "typeErrors":
      return failure.output.trimEnd();
    case "violations":
      return failure.violations.map((v) => JSON.stringify(v)).join("\n");
  }
}

function unlistedFiles(
  spec: LoadedSpec,
  typeChecked: Extract<TypeCheck, { readonly kind: "passed" }>,
): Found<Malformed>[] {
  const tsconfig = relative(spec.root, typeChecked.tsconfig).split(sep).join("/");
  return spec.sources
    .filter((s) => !typeChecked.includes(join(spec.root, s.file)))
    .map((s) => ({
      violation: { kind: "Malformed.unlistedFile", definition: null, data: { tsconfig } },
      place: { file: s.file, line: 1, column: 1 },
    }));
}

/**
 * checkSpec after `typeChecked`, the type check of `root`. A spec without a structure is unloadable unless a violation
 * says why, since the types let a definition name no definition of the spec only through `any` or an unexported value.
 */
export async function checkSpecWith(root: string, typeChecked: TypeCheck): Promise<SpecCheck> {
  if (typeChecked.kind !== "passed") return typeChecked;
  let loaded: Awaited<ReturnType<typeof loadSpec>>;
  try {
    loaded = await loadSpec(root);
  } catch (error) {
    return { kind: "unloadable", reason: reason(error) };
  }
  const { spec } = loaded;
  const structured = "unresolved" in spec ? undefined : spec;
  const malformed = [...unlistedFiles(spec, typeChecked), ...loaded.malformed];
  const loading = [
    ...malformed,
    ...syntaxChecks.flatMap((c) => c.check(spec)),
    ...(structured === undefined ? [] : structureChecks.flatMap((c) => c.check(structured))),
  ];
  const found: Found<Malformed | NonCanonical | Restricted | Illegal>[] =
    malformed.length > 0 || structured === undefined
      ? loading
      : [
          ...loading,
          ...validate(structured.structure).map((violation) => ({ violation, place: placeOfIllegal(spec, violation) })),
        ];
  if (found.length === 0) {
    if ("unresolved" in spec) return { kind: "unloadable", reason: `${spec.unresolved} names no definition` };
    return { kind: "checked", spec: spec as CheckedSpec };
  }
  const violations = found.sort(({ place: x }, { place: y }) => comparePlaces(x, y)).map(reportedOfFound);
  return { kind: "violations", files: spec.sources.length, violations };
}

/**
 * Type-checks the spec in the folder `root` with tsc on the nearest tsconfig.json at or above it, loads it, and checks
 * it, as a compiler compiles before it runs. When loading finds a Malformed violation, the structure (Illegal) goes
 * unchecked.
 */
export const checkSpec = (root: string): Promise<SpecCheck> => checkSpecWith(root, typeCheck(root, process.cwd()));
