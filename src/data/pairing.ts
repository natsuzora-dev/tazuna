import { existsSync, readdirSync } from "node:fs";

export interface Entry {
  readonly name: string;
  readonly kind: "file" | "folder" | "other";
}

export interface Pairing<T> {
  /** The expected values whose name has a <name>.jsonl file, in their order. */
  readonly paired: readonly T[];
  /** The expected values whose name has no <name>.jsonl file, in their order. */
  readonly missing: readonly T[];
  /** The names of <name>.jsonl files that no expected name has, in the order of the entries. */
  readonly extra: readonly string[];
  /** The names of the entries that are not <name>.jsonl files, in the order of the entries. */
  readonly unknown: readonly string[];
}

const extension = ".jsonl";

const fileName = (e: Entry): string | undefined =>
  e.kind === "file" && e.name.endsWith(extension) ? e.name.slice(0, -extension.length) : undefined;

/** Pairs the expected values, by `name`, with the <name>.jsonl files among the entries. */
export function pair<T>(name: (x: T) => string, expected: readonly T[], entries: readonly Entry[]): Pairing<T> {
  const names = entries.flatMap((e) => fileName(e) ?? []);
  const expectedNames = expected.map(name);
  return {
    paired: expected.filter((x) => names.includes(name(x))),
    missing: expected.filter((x) => !names.includes(name(x))),
    extra: names.filter((n) => !expectedNames.includes(n)),
    unknown: entries.filter((e) => fileName(e) === undefined).map((e) => e.name),
  };
}

/** Returns the entries of the folder sorted by name, or none when the folder does not exist. */
export function entriesOf(folder: string): Entry[] {
  if (!existsSync(folder)) return [];
  return readdirSync(folder, { withFileTypes: true })
    .map((e): Entry => ({ name: e.name, kind: e.isFile() ? "file" : e.isDirectory() ? "folder" : "other" }))
    .sort((a, b) => (a.name < b.name ? -1 : a.name > b.name ? 1 : 0));
}
