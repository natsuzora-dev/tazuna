import { join, relative, sep } from "node:path";
import { ask } from "../cli/engine.ts";
import { Converter } from "../convert/program.ts";
import type { Illegal } from "../data/illegal.generated.ts";
import { InternalError } from "../data/internalError.ts";
import type { Malformed } from "../data/malformed.ts";
import type { NonCanonical } from "../data/nonCanonical.ts";
import type { Restricted } from "../data/restricted.ts";
import type { ReportedViolation } from "../data/violation.ts";
import type { Place } from "../dsl/definition.ts";
import { comparePlaces, type Found, placeOf, reportedOfFound } from "../load/found.ts";
import { type Loaded, type LoadedSpec, loadSpec, type Spec } from "../load/load.ts";
import * as answers from "./nonCanonical/answers.ts";
import * as binds from "./nonCanonical/binds.ts";
import * as constants from "./nonCanonical/constants.ts";
import * as descriptions from "./nonCanonical/descriptions.ts";
import * as keywords from "./nonCanonical/keywords.ts";
import * as offers from "./nonCanonical/offers.ts";
import * as functions from "./restricted/functions.ts";
import * as schemas from "./restricted/schemas.ts";
import * as sources from "./restricted/sources.ts";
import { type TypeCheck, typeCheck } from "./typeCheck.ts";

declare const checked: unique symbol;
declare const convertedMark: unique symbol;

/** A spec in which checkSpec found no violation. Only checkSpec makes one. Its spec functions may be unconverted. */
export type CheckedSpec = Spec & { readonly [checked]: true };

/** A checked spec whose functions are converted to IR, which the engine needs to run the spec. */
export type ConvertedSpec = CheckedSpec & { readonly [convertedMark]: true };

/** Why checkSpec returned no checked spec. All but `typeErrors` and `violations` are usage errors. */
export type SpecFailure =
  | { readonly kind: "noTsconfig" }
  | { readonly kind: "noTypescript" }
  | { readonly kind: "unfinished"; readonly reason: string }
  | { readonly kind: "unloadable"; readonly reason: string }
  | { readonly kind: "typeErrors"; readonly output: string }
  | { readonly kind: "violations"; readonly files: number; readonly violations: readonly ReportedViolation[] };

export type SpecCheck<S extends CheckedSpec = CheckedSpec> =
  | SpecFailure
  | { readonly kind: "checked"; readonly spec: S };

const syntaxChecks: readonly { readonly check: (spec: LoadedSpec) => readonly Found<NonCanonical | Restricted>[] }[] = [
  answers,
  binds,
  constants,
  descriptions,
  keywords,
  offers,
  schemas,
  sources,
];

function placeOfIllegal(spec: Spec, illegal: Illegal): Place {
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
    case "Illegal.unlistedCaller":
    case "Illegal.restoredHeld":
    case "Illegal.inexactDelay":
    case "Illegal.negativeDelay":
    case "Illegal.unorderedSortKey":
    case "Illegal.defaultedMapKey":
    case "Illegal.ambiguousUnion":
      return placeOf(spec, illegal.definition);
  }
}

/** The NonCanonical and Illegal violations of the structure, which the engine finds, each at its place. */
function structureViolations(spec: Spec): Found<NonCanonical | Illegal>[] {
  const [checked] = ask("check", [{ structure: spec.structure }]);
  return [
    ...(checked?.nonCanonical ?? []).map((violation) => ({ violation, place: placeOf(spec, violation.definition) })),
    ...(checked?.illegal ?? []).map((violation) => ({ violation, place: placeOfIllegal(spec, violation) })),
  ];
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
 * The spec with its functions converted to IR, or the Restricted.function violations of what `converter` leaves
 * outside the IR. Without a converter, one runs for this spec alone.
 */
function converted(spec: Spec, converter: Converter | undefined): Spec | Found<Restricted>[] {
  const own = converter ?? new Converter();
  try {
    const { program, notConverted } = own.program(spec);
    const outside = functions.check(spec, notConverted);
    return outside.length > 0 ? outside : { ...spec, structure: { ...spec.structure, program } };
  } finally {
    if (converter === undefined) own.close();
  }
}

/** checkSpecWith, or with "unconverted" checkSpec, whose spec functions stay unchecked. */
async function checkWith(
  root: string,
  typeChecked: TypeCheck,
  converter: Converter | undefined | "unconverted",
): Promise<SpecCheck> {
  if (typeChecked.kind !== "passed") return typeChecked;
  let loaded: Loaded;
  try {
    loaded = await loadSpec(root);
  } catch (error) {
    if (error instanceof InternalError) throw error;
    return { kind: "unloadable", reason: reason(error) };
  }
  const { spec } = loaded;
  const unlisted = unlistedFiles(spec, typeChecked);
  const syntax = syntaxChecks.flatMap((c) => c.check(spec));
  const found: Found<Malformed | NonCanonical | Restricted | Illegal>[] =
    loaded.kind === "structured" && unlisted.length === 0
      ? [...syntax, ...structureViolations(loaded.spec)]
      : [...unlisted, ...(loaded.kind === "malformed" ? loaded.malformed : []), ...syntax];
  if (found.length === 0 && loaded.kind === "structured" && converter !== "unconverted") {
    const done = converted(loaded.spec, converter);
    if (!Array.isArray(done)) return { kind: "checked", spec: done as CheckedSpec };
    found.push(...done);
  }
  if (found.length === 0) return { kind: "checked", spec: loaded.spec as CheckedSpec };
  const violations = found.sort(({ place: x }, { place: y }) => comparePlaces(x, y)).map(reportedOfFound);
  return { kind: "violations", files: spec.sources.length, violations };
}

/**
 * Type-checks the spec in the folder `root` with tsc on the nearest tsconfig.json at or above it, loads it, and checks
 * it. A Malformed violation leaves the structure unchecked: Illegal, and the NonCanonical checks that read it. The spec
 * functions stay unconverted: a test runner that transforms the spec files, as vitest does, hides their source positions
 * from the converter.
 */
export const checkSpec = (root: string): Promise<SpecCheck> =>
  checkWith(root, typeCheck(root, process.cwd()), "unconverted");

/**
 * Checks the spec in the folder `root` after `typeChecked`, its type check, and converts its spec functions to IR.
 * `converter` reads the spec functions; a caller that checks many specs passes one, since each converter starts tsgo.
 */
export const checkSpecWith = (
  root: string,
  typeChecked: TypeCheck,
  converter?: Converter,
): Promise<SpecCheck<ConvertedSpec>> => checkWith(root, typeChecked, converter) as Promise<SpecCheck<ConvertedSpec>>;
