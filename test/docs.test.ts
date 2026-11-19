import assert from "node:assert/strict";
import { execFileSync } from "node:child_process";
import { cpSync, mkdirSync, mkdtempSync, readdirSync, readFileSync, rmSync, writeFileSync } from "node:fs";
import { join, posix } from "node:path";
import { test } from "node:test";
import { explain } from "../src/cli/explain.ts";
import { main } from "../src/cli/main.ts";
import { groups as groupInfos } from "../src/data/groups.ts";
import { groupNames, parseKind } from "../src/data/kinds.ts";
import { leanRoot, typeChecked } from "./examples.ts";

const root = join(import.meta.dirname, "..");
const read = (path: string) => readFileSync(join(root, path), "utf8");

/** The paths of the files that npm packs, relative to the package root. */
const packed: readonly string[] = (
  JSON.parse(
    execFileSync("npm", ["pack", "--dry-run", "--json", "--ignore-scripts"], { cwd: root, encoding: "utf8" }),
  ) as readonly { readonly files: readonly { readonly path: string }[] }[]
).flatMap((p) => p.files.map((f) => f.path));
const isPacked = (path: string) => packed.some((p) => p === path || p.startsWith(`${path}/`));

/** The markdown files that the package ships, which readers read in node_modules. */
const shipped = packed
  .filter((path) => path.endsWith(".md"))
  .toSorted()
  .map((path) => ({ path, text: read(path) }));
/** The shipped markdown for people: every shipped file but the agent skills. */
const docs = shipped.filter(({ path }) => !path.startsWith("skills/"));
const guarantees = read("docs/guarantees.md");

/** The declarations of lean/Tazuna outside comments: each name as written, its keyword, and its file. */
const declarations = readdirSync(leanRoot, { recursive: true, encoding: "utf8" })
  .filter((file) => file.endsWith(".lean"))
  .flatMap((file) => {
    const code = readFileSync(join(leanRoot, file), "utf8")
      .replace(/\/-[\s\S]*?-\//g, "")
      .replace(/--.*$/gm, "");
    return [
      ...code.matchAll(
        /^(?:@\[[^\]]*\]\s*)?(?:(?:private|protected|noncomputable|partial)\s+)*(theorem|def|abbrev|structure|inductive)\s+([^\s(:{[]+)/gm,
      ),
    ].map(([, keyword = "", name = ""]) => ({ keyword, name, file: `lean/Tazuna/${file}` }));
  });
const isTheorem = (name: string) =>
  declarations.some((d) => d.keyword === "theorem" && d.name === name && d.file.startsWith("lean/Tazuna/Thm/"));

const proven = guarantees.slice(guarantees.indexOf("## Proven properties"));
const namesIn = (list: string) => [...list.matchAll(/`([^`]+)`/g)].map((n) => n[1] ?? "");
/** The last cell of each body row of the tables under Proven properties: the theorems that prove the row. */
const theoremCells = proven
  .split("\n")
  .filter((line) => line.startsWith("| ") && !line.startsWith("| Property |"))
  .map((line) => line.slice(0, -" |".length).split(" | ").at(-1) ?? "");

test("Proven properties is the last section of docs/guarantees.md, and each of its rows cites the theorems that prove it", () => {
  assert.ok(!proven.includes("\n## "));
  assert.ok(theoremCells.length > 0);
  assert.deepEqual(
    theoremCells.filter((cell) => !/^`[\w.]+`(?:, `[\w.]+`)*$/.test(cell)),
    [],
  );
});

test("Each theorem that a doc cites is a theorem stated in lean/Tazuna/Thm: every name in a Theorems cell under Proven properties, and every name with an underscore elsewhere", () => {
  const cited = [
    ...theoremCells.flatMap(namesIn),
    ...docs.flatMap(({ text }) => [...text.matchAll(/`([a-z][A-Za-z0-9]*_\w*)`/g)].map((m) => m[1] ?? "")),
  ];
  assert.ok(cited.length > 0);
  assert.deepEqual(
    [...new Set(cited)].filter((name) => !isTheorem(name)),
    [],
  );
});

test("Each Lean name that a doc cites with its files is declared in each of them, in its namespace or not", () => {
  const cited = docs.flatMap(({ text }) =>
    [...text.matchAll(/`([\w.]+)` in ((?:`lean\/[\w/]+\.lean`(?:,? and |, )?)+)/g)].flatMap(
      ([, name = "", files = ""]) => namesIn(files).map((file) => ({ name, file })),
    ),
  );
  assert.ok(cited.length > 0);
  assert.deepEqual(
    cited.filter(
      ({ name, file }) =>
        !declarations.some((d) => (d.name === name || d.name.endsWith(`.${name}`)) && d.file === file),
    ),
    [],
  );
});

/** The words `<Group>.<name>` of `text` whose group is a violation group and that name no kind of it. */
const unknownKinds = (path: string, text: string, pattern: RegExp) =>
  [...text.matchAll(pattern)]
    .filter(([, group = ""]) => groupNames.some((g) => g === group))
    .map(([, group, name]) => `${group}.${name}`)
    .filter((kind) => parseKind(kind) === undefined)
    .map((kind) => `${path} ${kind}`);

test("Each violation kind that a shipped markdown file names is a kind of its group", () => {
  assert.deepEqual(unknownKinds("x", "`Fault.data` and `Fault.failedEnsures`", /`(\w+)\.(\w+)`/g), ["x Fault.data"]);
  assert.deepEqual(
    shipped.flatMap(({ path, text }) => unknownKinds(path, text, /`(\w+)\.(\w+)`/g)),
    [],
  );
});

test("Each violation kind that a doc comment in src names is a kind of its group", () => {
  const comments = (text: string) => [...text.matchAll(/\/\*\*[\s\S]*?\*\//g)].map((m) => m[0]).join("\n");
  const unknown = readdirSync(join(root, "src"), { recursive: true, encoding: "utf8" })
    .filter((f) => f.endsWith(".ts"))
    .flatMap((f) => unknownKinds(`src/${f}`, comments(read(`src/${f}`)), /\b([A-Z]\w+)\.(\w+)\b/g));
  assert.deepEqual(unknown, []);
});

/** The lines of a Markdown text outside fenced code blocks, each with its line number. */
const proseLines = (text: string) => {
  let fenced = false;
  return text.split("\n").flatMap((line, i) => {
    const fence = line.trimStart().startsWith("```");
    if (fence) fenced = !fenced;
    return fenced || fence ? [] : [{ number: i + 1, line }];
  });
};
const headings = (text: string) =>
  proseLines(text).flatMap(({ number, line }) => {
    const [, marks = "", title = ""] = /^(#+) (.*)$/.exec(line) ?? [];
    return marks === "" ? [] : [{ number, level: marks.length, title }];
  });
const withoutCode = (line: string) => line.replace(/`[^`]*`/g, "");
const withoutTicks = (line: string) => line.replace(/`/g, "");

/** The anchor of a heading, as GitHub writes it. */
const slug = (title: string) =>
  title
    .toLowerCase()
    .replace(/[^\w\s-]/g, "")
    .trim()
    .replace(/\s+/g, "-");

test("The package ships the docs, the skills, and the ToDo sample spec, without the sample's tsconfig.json and package.json", () => {
  for (const path of [
    "README.md",
    "docs/concepts.md",
    "docs/guarantees.md",
    "skills/tazuna/SKILL.md",
    "samples/todo/spec/todo/scenarios.ts",
  ])
    assert.ok(isPacked(path), path);
  for (const path of ["samples/todo/spec/tsconfig.json", "samples/todo/spec/package.json", "samples/todo/web"])
    assert.ok(!isPacked(path), path);
});

test("Each shipped skill has the frontmatter name of its folder and a description", () => {
  const skills = shipped.filter(({ path }) => path.startsWith("skills/"));
  assert.ok(skills.length > 0);
  for (const { path, text } of skills)
    assert.match(text, new RegExp(`^---\\nname: ${posix.basename(posix.dirname(path))}\\ndescription: \\S`), path);
});

test("Each relative link in a shipped markdown file resolves to a packed file or folder, and each anchor to a heading of its target", () => {
  const links = shipped.flatMap(({ path, text }) =>
    [...text.matchAll(/\]\(([^)\s]+)\)/g)]
      .map((m) => m[1] ?? "")
      .filter((link) => !/^https?:/.test(link))
      .map((link) => ({ path, link })),
  );
  assert.ok(links.some(({ link }) => link.includes("#")));
  const broken = links.filter(({ path, link }) => {
    const [file = "", anchor] = link.split("#");
    const target = file === "" ? path : posix.join(posix.dirname(path), file).replace(/\/$/, "");
    if (!isPacked(target)) return true;
    return anchor !== undefined && !headings(read(target)).some((h) => slug(withoutTicks(h.title)) === anchor);
  });
  assert.deepEqual(broken, []);
});

test("Each package path that a shipped markdown file names in code font is packed", () => {
  const paths = shipped.flatMap(({ path, text }) =>
    [...text.matchAll(/`node_modules\/@natsuzora-dev\/tazuna\/([^`]*)`/g)].map((m) => ({
      path,
      target: (m[1] ?? "").replace(/\/$/, ""),
    })),
  );
  assert.ok(paths.length > 0);
  assert.deepEqual(
    paths.filter(({ target }) => target !== "" && !isPacked(target)),
    [],
  );
});

test("Each command and option that a shipped markdown file names exists", async () => {
  const out: string[] = [];
  await main(["--help"], { cwd: root, log: (line) => out.push(line), error: () => {} });
  const usage = out.join("\n");
  const unknown = shipped.flatMap(({ path, text }) => [
    ...[...text.matchAll(/`npx tazuna (\w+)/g)]
      .map((m) => m[1] ?? "")
      .filter((command) => !new RegExp(`^ {2}${command} `, "m").test(usage))
      .map((command) => `${path} ${command}`),
    ...[...text.matchAll(/(?<![\w-])(--[a-z]+)\b/g)]
      .map((m) => m[1] ?? "")
      .filter((option) => option !== "--help" && !new RegExp(`^ {4}${option}\\b`, "m").test(usage))
      .map((option) => `${path} ${option}`),
  ]);
  assert.deepEqual(unknown, []);
});

/** The product and language names that a heading writes capitalized. */
const properNouns: ReadonlySet<string> = new Set(["GitHub", "Lean", "ToDo", "TypeScript", "Zod"]);

/** The structure rules of pstack technical-writing that a script can check. Each returns the lines that break it. */
const proseRules: readonly {
  readonly rule: string;
  readonly check: (text: string) => number[];
  readonly reported: string;
  readonly clean: string;
}[] = [
  {
    rule: "A page has one h1",
    check: (text) => {
      const titles = headings(text).filter((h) => h.level === 1);
      return titles.length === 0 ? [1] : titles.slice(1).map((h) => h.number);
    },
    reported: "# Guide\n\n# Reference",
    clean: "# Guide\n\n## Reference",
  },
  {
    rule: "A heading is at most one level below the heading before it",
    check: (text) =>
      headings(text)
        .filter((h, i, all) => h.level > (all[i - 1]?.level ?? 0) + 1)
        .map((h) => h.number),
    reported: "# Guide\n\n### Install",
    clean: "# Guide\n\n## Install\n\n### From npm\n\n## Use",
  },
  {
    rule: "A heading is at most level 3",
    check: (text) =>
      headings(text)
        .filter((h) => h.level > 3)
        .map((h) => h.number),
    reported: "# Guide\n\n## Install\n\n### From npm\n\n#### On macOS",
    clean: "# Guide\n\n## Install\n\n### From npm",
  },
  {
    rule: "A list is not nested",
    check: (text) =>
      proseLines(text)
        .filter(({ line }) => /^\s+(?:[-*+]|\d+\.) /.test(line))
        .map(({ number }) => number),
    reported: "- Run it.\n  - On macOS.",
    clean: "1. Run it.\n   It prints - and 2. as text.\n\n   ```sh\n   - not a list\n   ```",
  },
  {
    rule: "A heading is in sentence case, except for the names of products and languages",
    check: (text) =>
      headings(text)
        .filter((h) =>
          withoutCode(h.title)
            .split(/\s+/)
            .slice(1)
            .some((word) => /^[A-Z][a-z]/.test(word) && !properNouns.has(word.replace(/\W+$/, ""))),
        )
        .map((h) => h.number),
    reported: "# Install The Tool",
    clean: "# Install the `Tool` from npm with the CLI, and prove the ToDo sample in Lean",
  },
  {
    rule: "Prose joins sentences with periods, not semicolons",
    check: (text) =>
      proseLines(text)
        .filter(({ line }) => withoutCode(line).includes(";"))
        .map(({ number }) => number),
    reported: "It runs; it stops.",
    clean: "It runs. It stops. `a; b` is code.\n\n1. Run it.\n\n   ```ts\n   run();\n   ```",
  },
];

for (const { rule, check, reported, clean } of proseRules)
  test(`${rule}: each doc follows it, and the check reports its reported example and not its clean one`, () => {
    assert.notDeepEqual(check(reported), []);
    assert.deepEqual(check(clean), []);
    assert.deepEqual(
      docs.flatMap(({ path, text }) => check(text).map((line) => `${path}:${line}`)),
      [],
    );
  });

test("The table of who fixes a violation in docs/guarantees.md has one row per group of src/data/groups.ts, in its order and with its reportedBy and fixedIn", () => {
  const table = guarantees.slice(guarantees.indexOf("## Who fixes a violation"), guarantees.indexOf("## Detections"));
  const rows = table.split("\n").filter((line) => line.startsWith("| `"));
  assert.deepEqual(
    rows,
    Object.entries(groupInfos).map(
      ([group, { reportedBy, fixedIn }]) =>
        `| \`${group}\` | ${reportedBy.map((c) => `\`${c}\``).join(", ")} | ${fixedIn} |`,
    ),
  );
});

test("Only docs/guarantees.md, the reference page, has tables", () => {
  assert.deepEqual(
    docs
      .filter(({ path }) => path !== "docs/guarantees.md")
      .flatMap(({ path, text }) =>
        proseLines(text)
          .filter(({ line }) => line.trimStart().startsWith("|"))
          .map(({ number }) => `${path}:${number}`),
      ),
    [],
  );
});

const readme = read("README.md");
/** Each fenced block of README.md with its language and the last link before it, de-indented to the fence. */
const readmeBlocks = [...readme.matchAll(/^( *)```(\w*)\n([\s\S]*?)^ *```$/gm)].map((m) => {
  const [, indent = "", language = "", body = ""] = m;
  const links = [...readme.slice(0, m.index).matchAll(/\]\((samples\/[^)]+)\)/g)];
  return {
    language,
    code: body.replace(new RegExp(`^${indent}`, "gm"), ""),
    link: links.at(-1)?.[1],
  };
});
const sample = "samples/todo/spec";

test("Each TypeScript block of README.md appears verbatim in the sample file that the last link before it points to", () => {
  const blocks = readmeBlocks.filter((b) => b.language === "ts");
  assert.ok(blocks.length > 0);
  for (const { code, link } of blocks) {
    assert.ok(link !== undefined, code);
    assert.ok(read(link).includes(code), `${link} does not contain:\n${code}`);
  }
});

const sampleFiles = readdirSync(join(root, sample), { recursive: true, encoding: "utf8" }).filter(
  (f) => f.endsWith(".ts") && !f.includes("node_modules"),
);
const scenarioCount = sampleFiles
  .map((f) => [...read(`${sample}/${f}`).matchAll(/^export const \w+ = scenario\(/gm)].length)
  .reduce((a, b) => a + b, 0);

test("The file and scenario counts in README.md are the ToDo sample's: every scenario for a full run, one for --only", () => {
  assert.match(readme, new RegExp(`\`${sampleFiles.length} files: no violations\``));
  const counts = [...readme.matchAll(/`(\d+)\/(\d+) scenarios( \(--only\))?/g)];
  assert.ok(counts.length > 0);
  for (const [line, ran, all, only] of counts)
    assert.deepEqual([Number(ran), Number(all)], [only === undefined ? scenarioCount : 1, scenarioCount], line);
});

test("The README tutorial's broken scenario gives the violation line and summary that README.md shows, and explain names the scenario as the side at fault", async () => {
  const [, name = "", from = "", to = ""] =
    /change the expected answer of `(\w+)` from `([^`]+)` to `([^`]+)`/.exec(readme) ?? [];
  const summary = /followed by `([^`]+)`/.exec(readme)?.[1];
  const [shown] = readmeBlocks.filter((b) => b.language === "json" && b.code.startsWith('{"kind"'));
  assert.ok(shown !== undefined && summary !== undefined);
  const violation = JSON.parse(shown.code) as { readonly kind: string; readonly scenario: { readonly name: string } };
  mkdirSync(join(import.meta.dirname, ".fixtures"), { recursive: true });
  const project = mkdtempSync(join(import.meta.dirname, ".fixtures", "readme-"));
  try {
    cpSync(join(root, sample), join(project, "spec"), {
      recursive: true,
      filter: (src) => !src.includes("node_modules"),
    });
    const scenarios = join(project, "spec/todo/scenarios.ts");
    const text = readFileSync(scenarios, "utf8");
    const edited = text.replace(`answered(${name}, ${from})`, `answered(${name}, ${to})`);
    assert.notEqual(edited, text);
    writeFileSync(scenarios, edited);
    const out: string[] = [];
    const err: string[] = [];
    const only = `todo/${violation.scenario.name}`;
    await main(["test", "spec", "--only", only], {
      cwd: project,
      log: (line) => out.push(line),
      error: (line) => err.push(line),
      typeCheck: () => typeChecked,
    });
    assert.deepEqual(out, [shown.code.trim()]);
    assert.equal(err.at(-1)?.replace(/^1\/(\d+) scenarios \(--only\)/, "$1/$1 scenarios"), summary);
  } finally {
    rmSync(project, { recursive: true, force: true });
  }
  const explained = explain(violation.kind);
  assert.ok("markdown" in explained && explained.markdown.includes("\n- Side at fault: The scenario"));
  assert.match(readme, /says what the violation means and that the scenario is the side at fault/);
});
