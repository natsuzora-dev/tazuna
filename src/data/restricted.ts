export const nondeterministicGlobals = ["Date", "performance", "crypto", "process", "globalThis", "Intl"] as const;

export const nondeterministicMembers = [
  { object: "Math", property: "random" },
  { object: "Temporal", property: "Now" },
] as const;

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

type Of<Name extends string, Data> = {
  readonly kind: `Restricted.${Name}`;
  readonly definition: null;
  readonly data: Data;
};

/**
 * TypeScript code in a spec file that uses a restricted feature, because the feature breaks what the meaning assumes of
 * spec functions: determinism, sound types, and service boundaries.
 */
export type Restricted =
  /** The file reads the global `global`, whose value depends on the environment, such as the clock or the process. */
  | Of<"global", { readonly global: (typeof nondeterministicGlobals)[number] }>
  /** The file reads `object.property`, such as `Math.random` or `Temporal.Now`, whose value changes between runs. */
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
  | Of<"crossServiceImport", { readonly service: string }>;
