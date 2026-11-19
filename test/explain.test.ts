import assert from "node:assert/strict";
import { existsSync, readdirSync, readFileSync } from "node:fs";
import { join } from "node:path";
import { test } from "node:test";
import { parseSync } from "oxc-parser";
import { type Example, type Excerpt, type Explanations, explanationsPath } from "../src/cli/explain.ts";
import { groups } from "../src/data/groups.ts";
import type { Group } from "../src/data/violation.ts";
import { expected } from "./expected.ts";
import { allKinds, unexemplified } from "./kinds.ts";

const root = join(import.meta.dirname, "..");
const maxExcerptLines = 30;

const sourceOf = (group: string) => {
  const base = join(root, "src/data", group.charAt(0).toLowerCase() + group.slice(1));
  return readFileSync(existsSync(`${base}.generated.ts`) ? `${base}.generated.ts` : `${base}.ts`, "utf8");
};

/** The text of a doc comment's body: its paragraphs, each on one line. */
const docText = (body: string) =>
  body
    .split("\n")
    .map((line) => line.replace(/^\s*\*( |$)/, "").trimEnd())
    .join("\n")
    .trim()
    .split(/\n{2,}/)
    .map((p) => (p.startsWith("- ") ? p : p.replace(/\n/g, " ")))
    .join("\n\n");

const comment = String.raw`/\*\*((?:(?!\*/)[\s\S])*)\*/\s*`;

/**
 * The doc comment of a kind's member of its group's union: `{ readonly kind: "<kind>"` in a generated file, `Of<"<name>"`
 * in a TS one. Uncovered documents the parts of Obligation, whose kinds it prefixes.
 */
function meaningOf(kind: string): string | undefined {
  const [group = "", name = ""] = kind.split(".");
  const member = new RegExp(`${comment}\\|\\s*(?:\\{\\s*readonly kind: "${kind}"|\\(?Of<\\s*"${name}")`);
  const body = member.exec(sourceOf(group))?.[1];
  return body === undefined ? undefined : docText(body);
}

const groupDoc = (group: string) => {
  const body = new RegExp(`${comment}export type ${group}\\b`).exec(sourceOf(group))?.[1] ?? "";
  return /^.*?\.(?=\s|$)/.exec(docText(body))?.[0] ?? "";
};

const exampleRoots = (dir: string): string[] =>
  readdirSync(dir, { withFileTypes: true })
    .filter((e) => e.isDirectory() && e.name !== "__snapshots__")
    .flatMap((e) => exampleRoots(join(dir, e.name)))
    .concat(existsSync(join(dir, expected)) ? [dir] : []);

const specLines = (dir: string): number =>
  readdirSync(dir, { recursive: true, encoding: "utf8" })
    .filter((f) => f.endsWith(".ts"))
    .reduce((n, f) => n + readFileSync(join(dir, f), "utf8").split("\n").length, 0);

interface Reported {
  readonly kind: string;
  readonly data?: { readonly difference?: { readonly mismatch?: { readonly kind: string } } };
  readonly location: { readonly file: string; readonly line?: number };
}

/** The node of `program` spanning the most lines, at most maxExcerptLines, that holds all of line `line`. */
function enclosing(text: string, line: number): { readonly from: number; readonly to: number } {
  const starts = [0];
  for (const l of text.split("\n")) starts.push((starts.at(-1) ?? 0) + l.length + 1);
  const lineAt = (offset: number) => starts.findLastIndex((s) => s <= offset) + 1;
  const begin = starts[line - 1] ?? 0;
  const end = (starts[line] ?? text.length) - 1;
  let best = { from: line, to: line };
  const visit = (node: unknown): void => {
    if (typeof node !== "object" || node === null) return;
    if (Array.isArray(node)) {
      for (const child of node) visit(child);
      return;
    }
    const { start, end: stop } = node as { readonly start?: unknown; readonly end?: unknown };
    if (typeof start === "number" && typeof stop === "number" && start <= begin && stop >= end) {
      const span = { from: lineAt(start), to: lineAt(stop - 1) };
      if (span.to - span.from < maxExcerptLines && span.to - span.from > best.to - best.from) best = span;
    }
    for (const [key, value] of Object.entries(node)) if (key !== "parent") visit(value);
  };
  visit(parseSync("excerpt.ts", text).program);
  return best;
}

/** The lines around the location of a violation of the example `dir`, or undefined when it names no line. */
function excerptOf(dir: string, { file, line }: Reported["location"]): Excerpt | undefined {
  if (line === undefined) return undefined;
  const text = readFileSync(join(dir, file), "utf8");
  const { from, to } = file.endsWith(".ts") ? enclosing(text, line) : { from: line, to: line };
  const lines = text.split("\n").slice(from - 1, to);
  const indent = Math.min(...lines.filter((l) => l.trim() !== "").map((l) => l.length - l.trimStart().length));
  return { file, from, to, text: lines.map((l) => l.slice(indent)).join("\n") };
}

/** Whether `a` comes before `b` in lexicographic order. */
const before = (a: readonly number[], b: readonly number[]) => {
  const i = a.findIndex((x, j) => x !== b[j]);
  return i >= 0 && (a[i] ?? 0) < (b[i] ?? 0);
};

/**
 * The example of each kind: of the examples whose expected.jsonl reports it, the one with the fewest spec lines, and
 * its first line of the kind. A kind reported as itself wins over one in a ChoiceDependent difference, and a location
 * inside the example over one outside.
 */
function examples(): ReadonlyMap<string, Example> {
  const candidates = new Map<
    string,
    { readonly rank: readonly number[]; readonly dir: string; readonly line: string }
  >();
  for (const dir of exampleRoots(join(root, "test")).sort()) {
    const size = specLines(dir);
    for (const line of readFileSync(join(dir, expected), "utf8")
      .split("\n")
      .filter((l) => l !== "")) {
      const v = JSON.parse(line) as Reported;
      const outside = v.location.file.startsWith("..") ? 1 : 0;
      const nested = v.data?.difference?.mismatch?.kind;
      for (const [kind, rank] of [
        [v.kind, [0, outside, size]],
        ...(nested === undefined ? [] : [[nested, [1, outside, size]] as const]),
      ] as const) {
        const known = candidates.get(kind);
        const better = known === undefined || before(rank, known.rank);
        if (better) candidates.set(kind, { rank, dir, line });
      }
    }
  }
  return new Map(
    [...candidates].map(([kind, { dir, line }]) => {
      const excerpt = excerptOf(dir, (JSON.parse(line) as Reported).location);
      return [kind, excerpt === undefined ? { violation: line } : { excerpt, violation: line }];
    }),
  );
}

function explanations(): Explanations {
  const found = examples();
  return {
    groups: Object.fromEntries(Object.keys(groups).map((g) => [g, groupDoc(g)])) as Record<Group, string>,
    kinds: Object.fromEntries(
      allKinds.toSorted().map((kind) => {
        const example = found.get(kind);
        return [kind, { meaning: meaningOf(kind) ?? "", ...(example === undefined ? {} : { example }) }];
      }),
    ),
  };
}

const written = explanations();

test("explain.json holds the first sentence of each group's doc comment, and each kind's doc comment and example", (t) => {
  t.assert.fileSnapshot(written, explanationsPath, { serializers: [(v) => `${JSON.stringify(v, null, 2)}\n`] });
});

test("Each group and each kind has a doc comment", () => {
  assert.deepEqual(
    Object.entries(written.groups).filter(([, doc]) => doc === ""),
    [],
  );
  assert.deepEqual(
    Object.entries(written.kinds).filter(([, k]) => k.meaning === ""),
    [],
  );
});

test(`Each kind has an example whose excerpt has at most ${maxExcerptLines} lines, except the unexemplified kinds and the InvalidScenario kinds, whose examples are data scenarios under test/sim with no spec of their own`, () => {
  const exempt = (kind: string) => kind in unexemplified || kind.startsWith("InvalidScenario.");
  assert.deepEqual(
    Object.entries(written.kinds)
      .filter(([kind, k]) => exempt(kind) === (k.example !== undefined))
      .map(([kind]) => kind),
    [],
  );
  assert.deepEqual(
    Object.keys(unexemplified).filter((kind) => !allKinds.includes(kind)),
    [],
  );
  assert.deepEqual(
    Object.entries(written.kinds)
      .filter(
        ([, k]) => k.example?.excerpt !== undefined && k.example.excerpt.to - k.example.excerpt.from >= maxExcerptLines,
      )
      .map(([kind]) => kind),
    [],
  );
});
