import { existsSync, readdirSync, readFileSync, writeFileSync } from "node:fs";
import { join } from "node:path";
import { parseSync } from "oxc-parser";
import { type Example, type Excerpt, type Explanations, explanationsPath } from "../src/cli/explain.ts";
import { groupNames, isUserKind, type Kind, kindsOf, parseKind, type UserKind } from "../src/data/kinds.ts";
import type { Group } from "../src/data/violation.ts";

const root = join(import.meta.dirname, "..");
const expected = "expected.jsonl";

/** The sources of a group's type: its TS file, then its generated file, either of which may be missing. */
const sourceOf = (group: Group): string => {
  const base = join(root, "src/data", group.charAt(0).toLowerCase() + group.slice(1));
  return [`${base}.ts`, `${base}.generated.ts`]
    .filter((file) => existsSync(file))
    .map((file) => readFileSync(file, "utf8"))
    .join("\n");
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
 * The doc comment of a kind's member of its group's union, or of the group's one member: `{ readonly kind: "<kind>"` in
 * a generated file, `Of<"<name>"` in a TS one. Uncovered documents the parts of Obligation, whose kinds it prefixes.
 */
function meaningOf(kind: Kind, group: Group): string {
  const name = kind.slice(group.length + 1);
  const member = new RegExp(`${comment}\\|?\\s*(?:\\{\\s*readonly kind: "${kind}"|\\(?Of<\\s*"${name}")`);
  const body = member.exec(sourceOf(group))?.[1];
  return body === undefined ? "" : docText(body);
}

const groupDoc = (group: Group) => {
  const body = new RegExp(`${comment}export type ${group}\\b`).exec(sourceOf(group))?.[1] ?? "";
  return /^.*?\.(?=\s|$)/.exec(docText(body))?.[0] ?? "";
};

/** The example of each kind: the folder under test named after the kind, which reports only that kind. */
export function exampleFolders(dir = join(root, "test")): readonly (readonly [Kind, string])[] {
  return readdirSync(dir, { withFileTypes: true })
    .filter((e) => e.isDirectory())
    .flatMap((e) => {
      const kind = parseKind(e.name)?.kind;
      return kind === undefined ? exampleFolders(join(dir, e.name)) : [[kind, join(dir, e.name)] as const];
    });
}

interface Reported {
  readonly location: { readonly file: string; readonly line?: number };
}

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

/** The first violation that the example `dir` reports, and the excerpt at its location if it names a line. */
function exampleOf(dir: string): Example {
  const [line = "{}"] = readFileSync(join(dir, expected), "utf8").split("\n");
  const excerpt = excerptOf(dir, (JSON.parse(line) as Reported).location);
  return { ...(excerpt === undefined ? {} : { excerpt }), violation: line };
}

/** The data of explain.json, from the doc comments in src/data and the examples under test. */
export function explanations(): Explanations {
  const examples = new Map(exampleFolders());
  const explanation = (kind: UserKind, group: Group) => {
    const dir = examples.get(kind);
    return { meaning: meaningOf(kind, group), ...(dir === undefined ? {} : { example: exampleOf(dir) }) };
  };
  const entries = groupNames
    .flatMap((group) =>
      kindsOf[group].flatMap((kind: Kind) => (isUserKind(kind) ? [[kind, explanation(kind, group)] as const] : [])),
    )
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
