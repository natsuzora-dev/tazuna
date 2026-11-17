import { join, relative, sep } from "node:path";
import type { Illegal } from "../data/illegal.generated.ts";
import type { Malformed } from "../data/malformed.ts";
import type { NonCanonical } from "../data/nonCanonical.ts";
import type { Restricted } from "../data/restricted.ts";
import type { ReportedViolation } from "../data/violation.ts";
import type { Place } from "../dsl/definition.ts";
import { comparePlaces, type Found, placeOf, reportedOfFound } from "../load/found.ts";
import { loadSpec, type Spec } from "../load/load.ts";
import { check as validate } from "../validation/check.ts";
import * as binds from "./nonCanonical/binds.ts";
import * as charts from "./nonCanonical/charts.ts";
import * as constants from "./nonCanonical/constants.ts";
import * as descriptions from "./nonCanonical/descriptions.ts";
import * as rejections from "./nonCanonical/rejections.ts";
import * as sources from "./restricted/sources.ts";
import { type TypeCheck, typeCheck } from "./typeCheck.ts";

declare const checked: unique symbol;

/** A spec in which checkSpec found no violation. Only checkSpec makes one. */
export type CheckedSpec = Spec & { readonly [checked]: true };

/**
 * The result of checkSpec: the checked spec, or why there is none. `noTsconfig`, `noTypescript`, `unfinished`, and
 * `unloadable` (a spec file threw when imported) are usage errors; `typeErrors` holds tsc's output.
 */
export type SpecCheck =
  | Exclude<TypeCheck, { readonly kind: "ran" }>
  | { readonly kind: "typeErrors"; readonly output: string }
  | { readonly kind: "unloadable"; readonly reason: string }
  | { readonly kind: "violations"; readonly files: number; readonly violations: readonly ReportedViolation[] }
  | { readonly kind: "checked"; readonly spec: CheckedSpec };

const syntaxChecks: readonly { readonly check: (spec: Spec) => readonly Found<NonCanonical | Restricted>[] }[] = [
  binds,
  charts,
  constants,
  descriptions,
  rejections,
  sources,
];

function placeOfIllegal(spec: Spec, illegal: Illegal): Place {
  switch (illegal.kind) {
    case "Illegal.foreignMember": {
      const contract = spec.contracts.find((c) => c.service === illegal.data.contract);
      if (contract === undefined) throw new Error(`no contract of ${illegal.data.contract}`);
      return contract.place;
    }
    case "Illegal.automationCycle":
    case "Illegal.missingParent":
    case "Illegal.ownQuery":
    case "Illegal.unlistedControl":
    case "Illegal.alwaysCycle":
    case "Illegal.foreignEvent":
    case "Illegal.indexReason":
      return placeOf(spec, illegal.definition);
  }
}

/** Returns the header lines of Node's error and the first stack frame outside node: internals. */
export function reason(error: unknown): string {
  if (!(error instanceof Error)) return String(error);
  const lines = (error.stack ?? error.message).split("\n");
  const frames = lines.findIndex((line) => line.startsWith("    at "));
  if (frames === -1) return lines.join("\n");
  const own = lines.slice(frames).find((line) => !line.includes("(node:") && !line.includes(" node:"));
  return [...lines.slice(0, frames), ...(own === undefined ? [] : [own])].join("\n");
}

function unlistedFiles(spec: Spec, typeChecked: Extract<TypeCheck, { readonly kind: "ran" }>): Found<Malformed>[] {
  const tsconfig = relative(spec.root, typeChecked.tsconfig).split(sep).join("/");
  return spec.sources
    .filter((s) => !typeChecked.includes(join(spec.root, s.file)))
    .map((s) => ({
      violation: { kind: "Malformed.unlistedFile", definition: null, data: { tsconfig } },
      place: { file: s.file, line: 1, column: 1 },
    }));
}

/**
 * Type-checks the spec in the folder `root` with tsc on the nearest tsconfig.json at or above it, loads it, and checks
 * it, as a compiler compiles before it runs. When loading finds a Malformed violation, the structure (Illegal) goes
 * unchecked.
 */
export async function checkSpec(
  root: string,
  typeChecker: (root: string) => TypeCheck = (r) => typeCheck(r, process.cwd()),
): Promise<SpecCheck> {
  const typeChecked = typeChecker(root);
  if (typeChecked.kind !== "ran") return typeChecked;
  if (!typeChecked.passed) return { kind: "typeErrors", output: typeChecked.output };
  let loaded: Awaited<ReturnType<typeof loadSpec>>;
  try {
    loaded = await loadSpec(root);
  } catch (error) {
    return { kind: "unloadable", reason: reason(error) };
  }
  const { spec } = loaded;
  const malformed = [...unlistedFiles(spec, typeChecked), ...loaded.malformed];
  const loading = [...malformed, ...syntaxChecks.flatMap((c) => c.check(spec))];
  const found: Found<Malformed | NonCanonical | Restricted | Illegal>[] =
    malformed.length > 0
      ? loading
      : [
          ...loading,
          ...validate(spec.structure).map((violation) => ({ violation, place: placeOfIllegal(spec, violation) })),
        ];
  if (found.length === 0) return { kind: "checked", spec: spec as CheckedSpec };
  const violations = found.sort(({ place: x }, { place: y }) => comparePlaces(x, y)).map(reportedOfFound);
  return { kind: "violations", files: spec.sources.length, violations };
}
