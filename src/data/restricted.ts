import type { DefinitionRef } from "./definitionRef.ts";

export const nondeterministicGlobals = [
  "Date",
  "Temporal",
  "performance",
  "crypto",
  "process",
  "globalThis",
  "Intl",
] as const;

export const nondeterministicMembers = [{ object: "Math", property: "random" }] as const;

/** The objects of nondeterministicMembers, which a spec file reads only through their members. */
export const memberObjects = [...new Set(nondeterministicMembers.map((m) => m.object))];

/** The methods whose result depends on the locale of the environment. */
export const localeMethods = [
  "localeCompare",
  "toLocaleString",
  "toLocaleDateString",
  "toLocaleTimeString",
  "toLocaleUpperCase",
  "toLocaleLowerCase",
] as const;

export const cryptoModules = ["crypto", "node:crypto"] as const;

export const suppressionMarks = [
  "biome-ignore",
  "@ts-ignore",
  "@ts-expect-error",
  "@ts-nocheck",
  "eslint-disable",
] as const;

/** The collection methods whose callback can read the index of the element as its second parameter. */
export const indexedMethods = ["map", "filter", "some", "every", "flatMap", "forEach", "find", "findIndex"] as const;

/** The schema features that Lean can neither parse nor encode to SMT, which a spec finds outside tazuna instead. */
export const schemaFeatures = [
  "codec",
  "refinement",
  "overwrite",
  "stringFormat",
  "record",
  "tuple",
  "recursion",
  "message",
] as const;

type Of<Name extends string, Data, Definition = null> = {
  readonly kind: `Restricted.${Name}`;
  readonly definition: Definition;
  readonly data: Data;
};

type SchemaPlace = { readonly path: readonly string[]; readonly feature: (typeof schemaFeatures)[number] };

/**
 * TypeScript code in a spec file that uses a restricted feature, because the feature breaks what the meaning assumes of
 * spec functions: determinism, sound types, and service boundaries.
 */
export type Restricted =
  /**
   * The file reads the global `global`, whose value depends on the environment, such as the clock, the process, or the
   * time zone rules of `Temporal`. A spec function reads time from `now` and holds it with tazuna's `instant`,
   * `duration` and `date`; what needs a time zone, such as today's date, comes from an external service.
   */
  | Of<"global", { readonly global: (typeof nondeterministicGlobals)[number] }>
  /** The file reads `object.property`, such as `Math.random`, whose value changes between runs. */
  | Of<"member", (typeof nondeterministicMembers)[number]>
  /** The file reads `object` whole, so it could reach a restricted member under another name. */
  | Of<"alias", { readonly object: (typeof memberObjects)[number] }>
  /** The file calls `method`, whose result depends on the locale of the environment. */
  | Of<"localeMethod", { readonly method: (typeof localeMethods)[number] }>
  /** The file declares a module-level `let` or `var`, through which a spec function could keep state between calls. */
  | Of<"mutableModule", { readonly declaration: "let" | "var" }>
  /** The file imports `module`, whose functions return random values. */
  | Of<"cryptoImport", { readonly module: (typeof cryptoModules)[number] }>
  /** The file uses a non-null assertion (`!`), which tells tsc that a value is defined without checking it. */
  | Of<"nonNull", Readonly<Record<string, never>>>
  /** The file casts a value to `type` with `as`, which tells tsc a type without checking it. `as const` is allowed. */
  | Of<"as", { readonly type: string }>
  /** The file writes the type `any`, which turns off tsc's checks of every value of that type. */
  | Of<"any", Readonly<Record<string, never>>>
  /** The file has the mark `mark`, which silences tsc or the linter. */
  | Of<"suppression", { readonly mark: (typeof suppressionMarks)[number] }>
  /** A file of one service imports from the service `service` anything other than its contract. */
  | Of<"crossServiceImport", { readonly service: string }>
  /**
   * The file passes `method` a callback that reads the index of the element, its second parameter. A spec reads an
   * order through a field that holds it, or through sortedBy and the methods of a Bag.
   */
  | Of<"indexCallback", { readonly method: (typeof indexedMethods)[number] }>
  /**
   * The schema at `path` of the definition, or of the constants `name` when `definition` is null, uses `feature`,
   * which Lean can neither parse nor encode to SMT. In its place:
   * - `codec` (z.codec, a pipe, a transform): the value as the wire holds it, which spec functions compute from.
   * - `refinement` (refine, superRefine, check): a requires or an invariant that states the condition.
   * - `overwrite` (overwrite, trim, toLowerCase, toUpperCase, z.coerce): the value as given, with the condition in a
   *   requires.
   * - `stringFormat` (email, url, regex, uuid and the other formats but startsWith, endsWith, includes and date): a
   *   z.string() whose format an external service or the implementation checks.
   * - `record` (z.record): an array of objects with a key field, or an entity.
   * - `tuple` (z.tuple): an object with a field per position.
   * - `recursion` (z.lazy): an entity whose rows ref() each other.
   * - `message`: an error message that is a function; a message written as a string stays.
   */
  | Of<"schema", SchemaPlace | (SchemaPlace & { readonly name: string }), DefinitionRef | null>
  /**
   * A spec function of the definition holds a construct that tazuna can neither execute in Lean nor encode to SMT,
   * which `reason` names with the construct's source. In its place:
   * - a statement other than `const`, `if` and `return`, such as `let`, a loop, or `push`: an expression, such as
   *   `map`, `filter` or `sum` of a Bag.
   * - `throw`: a `requires`, guard, or invariant that states the condition.
   * - a name declared outside the function, such as a parameter of a function that builds definitions: a constant,
   *   or a value that the input, the records or the context hold, with one definition per value.
   * - a call that the IR does not have, such as `trim`, `Object.keys`, `flatMap` or `JSON.parse`: the value held in
   *   a field, or a helper declared with `const` at the top of the file.
   * - an event that the command's `emits` does not list: the event added to `emits`.
   */
  | Of<"function", { readonly reason: string }, DefinitionRef>;
