import { readFileSync } from "node:fs";
import { extname, join } from "node:path";
import { groups } from "../data/groups.ts";
import type { Group } from "../data/violation.ts";

/** The lines `from` to `to` of a file of an example's spec, which hold the place that its violation names. */
export interface Excerpt {
  readonly file: string;
  readonly from: number;
  readonly to: number;
  readonly text: string;
}

/** A violation line that one of tazuna's test examples reports, and the excerpt at its location if it names a line. */
export interface Example {
  readonly excerpt?: Excerpt;
  readonly violation: string;
}

/**
 * The data that `explain` prints: the first sentence of each group's doc comment, and each kind's doc comment and
 * example. test/explain.test.ts writes it to explain.json from src/data and the test examples, which the package does
 * not ship.
 */
export interface Explanations {
  readonly groups: Readonly<Record<Group, string>>;
  readonly kinds: Readonly<Record<string, { readonly meaning: string; readonly example?: Example }>>;
}

export const explanationsPath = join(import.meta.dirname, "../../explain.json");

const fence = (lang: string, text: string) => `\`\`\`${lang}\n${text}\n\`\`\``;

const excerptText = ({ file, from, to, text }: Excerpt) => [
  `\`${file}\`, ${from === to ? `line ${from}` : `lines ${from} to ${to}`}:`,
  "",
  fence(extname(file) === ".ts" ? "ts" : "json", text),
  "",
];

/** Returns the markdown that explains `kind`, or undefined when it is no violation kind. */
export function explain(kind: string): string | undefined {
  const explanations = JSON.parse(readFileSync(explanationsPath, "utf8")) as Explanations;
  const known = Object.hasOwn(explanations.kinds, kind) ? explanations.kinds[kind] : undefined;
  if (known === undefined) return undefined;
  const group = kind.slice(0, kind.indexOf(".")) as Group;
  const { reportedBy, fixedIn } = groups[group];
  const { example } = known;
  return [
    `# ${kind}`,
    "",
    known.meaning,
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
}
