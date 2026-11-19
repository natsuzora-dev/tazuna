import { existsSync, readFileSync } from "node:fs";
import { extname, join } from "node:path";
import { groups } from "../data/groups.ts";
import { type Kind, parseKind } from "../data/kinds.ts";
import type { Group } from "../data/violation.ts";

/** The lines `from` to `to` of a file of an example's spec: the top-level statement that holds `line`, the reported one. */
export interface Excerpt {
  readonly file: string;
  readonly from: number;
  readonly to: number;
  readonly line: number;
  readonly text: string;
}

/** A violation that the test example named after its kind reports, and the excerpt at its location if it names a line. */
export interface Example {
  readonly excerpt?: Excerpt;
  readonly violation: string;
}

/**
 * The data that `explain` prints: the first sentence of each group's doc comment, and each kind's doc comment and
 * example. scripts/explain.ts builds it from src/data and the test examples, which the package does not ship.
 */
export interface Explanations {
  readonly groups: Readonly<Record<Group, string>>;
  readonly kinds: Readonly<Record<Kind, { readonly meaning: string; readonly example?: Example }>>;
}

export const explanationsPath = join(import.meta.dirname, "../../explain.json");

const fence = (lang: string, text: string) => `\`\`\`${lang}\n${text}\n\`\`\``;

/** The excerpt with a line-number gutter, `>` marking the reported line. */
function excerptText({ file, from, to, line, text }: Excerpt): string[] {
  const width = String(to).length;
  const gutter = text
    .split("\n")
    .map((code, i) => `${from + i === line ? ">" : " "} ${String(from + i).padStart(width)} | ${code}`.trimEnd());
  return [
    `\`${file}\`, line ${line} marked:`,
    "",
    fence(extname(file) === ".ts" ? "ts" : "json", gutter.join("\n")),
    "",
  ];
}

/**
 * The markdown that explains the kind that `text` names, from the explanations at `path`, or a misuse when `text` names
 * no kind or `path` is missing.
 */
export function explain(
  text: string,
  path = explanationsPath,
): { readonly markdown: string } | { readonly misuse: string } {
  const parsed = parseKind(text);
  if (parsed === undefined) return { misuse: `unknown kind ${text}` };
  if (!existsSync(path)) return { misuse: `${path} is missing. Reinstall tazuna` };
  const explanations = JSON.parse(readFileSync(path, "utf8")) as Explanations;
  const { kind, group } = parsed;
  const { meaning, example } = explanations.kinds[kind];
  const { reportedBy, fixedIn } = groups[group];
  const markdown = [
    `# ${kind}`,
    "",
    meaning,
    "",
    `${group}: ${explanations.groups[group]}`,
    "",
    `- Reported by: ${reportedBy.map((c) => `\`${c}\``).join(", ")}`,
    `- Side at fault: ${fixedIn}`,
    ...(example === undefined
      ? []
      : [
          "",
          "## Example",
          "",
          ...(example.excerpt === undefined ? [] : excerptText(example.excerpt)),
          "The violation:",
          "",
          fence("json", example.violation),
        ]),
  ].join("\n");
  return { markdown };
}
