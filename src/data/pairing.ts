import { existsSync, readdirSync } from "node:fs";

export interface Entry {
  readonly name: string;
  readonly kind: "file" | "folder" | "other";
}

export interface Pairing {
  /** The expected names that have a <name>.jsonl file, in the order of the expected names. */
  readonly paired: readonly string[];
  /** The expected names that have no <name>.jsonl file, in the order of the expected names. */
  readonly missing: readonly string[];
  /** The names of <name>.jsonl files that no expected name has, in the order of the entries. */
  readonly extra: readonly string[];
  /** The names of the entries that are not <name>.jsonl files, in the order of the entries. */
  readonly unknown: readonly string[];
}

const extension = ".jsonl";

const fileName = (e: Entry): string | undefined =>
  e.kind === "file" && e.name.endsWith(extension) ? e.name.slice(0, -extension.length) : undefined;

/** Pairs the expected names with the <name>.jsonl files among the entries. */
export function pair(expected: readonly string[], entries: readonly Entry[]): Pairing {
  const names = entries.flatMap((e) => fileName(e) ?? []);
  return {
    paired: expected.filter((n) => names.includes(n)),
    missing: expected.filter((n) => !names.includes(n)),
    extra: names.filter((n) => !expected.includes(n)),
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
