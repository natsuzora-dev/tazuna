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
 * spec functions: determinism, sound types, and service boundaries. `crossServiceImport` is a file of one service that
 * imports from the service `service` anything other than its contract.
 */
export type Restricted =
  | Of<"global", { readonly global: (typeof nondeterministicGlobals)[number] }>
  | Of<"member", (typeof nondeterministicMembers)[number]>
  | Of<"alias", { readonly object: (typeof memberObjects)[number] }>
  | Of<"localeMethod", { readonly method: (typeof localeMethods)[number] }>
  | Of<"mutableModule", { readonly declaration: "let" | "var" }>
  | Of<"cryptoImport", { readonly module: (typeof cryptoModules)[number] }>
  | Of<"nonNull", Readonly<Record<string, never>>>
  | Of<"as", { readonly type: string }>
  | Of<"suppression", { readonly mark: (typeof suppressionMarks)[number] }>
  | Of<"crossServiceImport", { readonly service: string }>;
