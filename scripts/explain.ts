import { existsSync, readdirSync, readFileSync, writeFileSync } from "node:fs";
import { join } from "node:path";
import { parseSync } from "oxc-parser";
import { type Example, type Excerpt, type Explanations, explanationsPath } from "../src/cli/explain.ts";
import { groupNames, type Kind, kindsOf } from "../src/data/kinds.ts";
import type { Group } from "../src/data/violation.ts";

const root = join(import.meta.dirname, "..");
const expected = "expected.jsonl";

const sourceOf = (group: Group): string => {
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
function meaningOf(kind: Kind, group: Group): string {
  const name = kind.slice(group.length + 1);
  const member = new RegExp(`${comment}\\|\\s*(?:\\{\\s*readonly kind: "${kind}"|\\(?Of<\\s*"${name}")`);
  const body = member.exec(sourceOf(group))?.[1];
  return body === undefined ? "" : docText(body);
}

const groupDoc = (group: Group) => {
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
  readonly kind: Kind;
  readonly data?: { readonly difference?: { readonly mismatch?: { readonly kind: Kind } } };
  readonly location: { readonly file: string; readonly line?: number };
}

/** A violation line of an example that reports `kind`, as itself or as the mismatch of a ChoiceDependent difference. */
interface Candidate {
  readonly kind: Kind;
  /** The kind of the reported violation whose difference holds `violation`, when that is nested. */
  readonly within?: Kind;
  readonly violation: object;
  readonly location: Reported["location"];
  readonly dir: string;
  readonly size: number;
}

/** The criteria by which one example is preferred to another, in order: the lower value wins. */
const preferences: readonly ((c: Candidate) => number)[] = [
  (c) => (c.within === undefined ? 0 : 1),
  (c) => (c.location.file.startsWith("..") ? 1 : 0),
  (c) => (c.location.line === undefined ? 1 : 0),
  (c) => c.size,
];

const byPreference = (a: Candidate, b: Candidate) => preferences.map((p) => p(a) - p(b)).find((d) => d !== 0) ?? 0;

/** The lines of the top-level statement of the spec file `text` that holds line `line`. */
function statementAt(file: string, text: string, line: number): Pick<Excerpt, "from" | "to"> {
  const starts = [0];
  for (const l of text.split("\n")) starts.push((starts.at(-1) ?? 0) + l.length + 1);
  const lineAt = (offset: number) => starts.findLastIndex((s) => s <= offset) + 1;
  const statement = parseSync(file, text).program.body.find(
    (s) => lineAt(s.start) <= line && line <= lineAt(s.end - 1),
  );
  if (statement === undefined) throw new Error(`${file}:${line} is in no top-level statement`);
  return { from: lineAt(statement.start), to: lineAt(statement.end - 1) };
}

/** The excerpt at the location of a violation of the example `dir`, or undefined when it names no line. */
function excerptOf(dir: string, { file, line }: Reported["location"]): Excerpt | undefined {
  if (line === undefined) return undefined;
  const source = readFileSync(join(dir, file), "utf8");
  const { from, to } = file.endsWith(".ts") ? statementAt(file, source, line) : { from: line, to: line };
  return {
    file,
    from,
    to,
    line,
    text: source
      .split("\n")
      .slice(from - 1, to)
      .join("\n"),
  };
}

function candidates(): Candidate[] {
  return exampleRoots(join(root, "test"))
    .sort()
    .flatMap((dir) => {
      const size = specLines(dir);
      return readFileSync(join(dir, expected), "utf8")
        .split("\n")
        .filter((l) => l !== "")
        .flatMap((line): Candidate[] => {
          const v = JSON.parse(line) as Reported;
          const nested = v.data?.difference?.mismatch;
          const own = { kind: v.kind, violation: v, location: v.location, dir, size };
          return nested === undefined ? [own] : [own, { ...own, kind: nested.kind, violation: nested, within: v.kind }];
        });
    });
}

function exampleOf(c: Candidate): Example {
  const excerpt = excerptOf(c.dir, c.location);
  return {
    ...(excerpt === undefined ? {} : { excerpt }),
    violation: JSON.stringify(c.violation),
    ...(c.within === undefined ? {} : { within: c.within }),
  };
}

/** The data of explain.json, from the doc comments in src/data and the examples under test. */
export function explanations(): Explanations {
  const all = candidates().sort(byPreference);
  const explanation = (kind: Kind, group: Group) => {
    const best = all.find((c) => c.kind === kind);
    return { meaning: meaningOf(kind, group), ...(best === undefined ? {} : { example: exampleOf(best) }) };
  };
  const entries = groupNames
    .flatMap((group) => kindsOf[group].map((kind: Kind) => [kind, explanation(kind, group)] as const))
    .sort(([a], [b]) => (a < b ? -1 : 1));
  return {
    groups: Object.fromEntries(groupNames.map((g) => [g, groupDoc(g)])) as Explanations["groups"],
    kinds: Object.fromEntries(entries) as Explanations["kinds"],
  };
}

if (import.meta.main) {
  const built = `${JSON.stringify(explanations(), null, 2)}\n`;
  if (process.argv.includes("--write")) writeFileSync(explanationsPath, built);
  else if (!existsSync(explanationsPath) || readFileSync(explanationsPath, "utf8") !== built) {
    console.error("explain.json differs from what scripts/explain.ts builds. Run npm run explain:write.");
    process.exit(1);
  }
}
