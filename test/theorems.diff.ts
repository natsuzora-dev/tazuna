import assert from "node:assert/strict";
import { execFileSync } from "node:child_process";
import { readdirSync, readFileSync, statSync } from "node:fs";
import { homedir } from "node:os";
import { join } from "node:path";
import { test } from "node:test";

const repo = join(import.meta.dirname, "..");
const lean = join(repo, "lean");
const thmDir = join(lean, "Tazuna/Thm");

interface Decl {
  readonly kind: string;
  readonly module: string;
  readonly name: string;
  readonly uses: string[];
}

/** The declarations of Tazuna and the declarations that each uses, from tazuna-graph. */
function graph(): Map<string, Decl> {
  const out = execFileSync("lake", ["exe", "tazuna-graph"], {
    cwd: lean,
    encoding: "utf8",
    maxBuffer: 1 << 28,
    env: { ...process.env, PATH: `${join(homedir(), ".elan/bin")}:${process.env["PATH"] ?? ""}` },
  });
  const decls = new Map<string, Decl>();
  for (const line of out.split("\n").filter(Boolean)) {
    const [kind = "", module = "", name = "", uses = ""] = line.split("\t");
    decls.set(name, { kind, module, name, uses: uses.split(" ").filter(Boolean) });
  }
  return decls;
}

const last = (name: string) => name.split(".").at(-1) ?? name;

/** The files outside lean/Tazuna that may name a theorem: docs, src, test, the viewer, samples, and the Lean tools. */
const textFiles = (dir: string): string[] =>
  readdirSync(dir).flatMap((entry) => {
    if (["node_modules", ".lake", "dist", ".git", "Tazuna", ".claude"].includes(entry)) return [];
    const path = join(dir, entry);
    if (statSync(path).isDirectory()) return textFiles(path);
    return /\.(md|ts|tsx|lean|json|js)$/.test(entry) ? [path] : [];
  });

const declRe =
  /^(?:@\[[^\]]*\]\s*)?(?:(?:private|protected|noncomputable|partial)\s+)*(theorem|lemma|def|abbrev|instance|structure|inductive)\s+([^\s(:{[]+)/;

/**
 * The declarations of lean/Tazuna/Thm that nothing reaches. Roots are every declaration outside Tazuna.Thm, every Thm
 * declaration whose name a file outside lean/Tazuna mentions, and every Thm name that a Thm command other than a
 * declaration writes (`open X (a b)`, `attribute [simp] a`). Edges are the constants that a declaration uses, plus the
 * Thm names that its `simp`, `unfold`, or `agree` lists write, since an rfl lemma that `simp only` unfolds leaves no
 * trace in the proof term.
 */
function unreached(decls: Map<string, Decl>): string[] {
  const inThm = (d: Decl) => d.module.startsWith("Tazuna.Thm.");
  const words = new Set<string>();
  for (const file of textFiles(repo))
    for (const m of readFileSync(file, "utf8").matchAll(/[A-Za-z_][\w.']*/g)) {
      words.add(m[0]);
      for (const part of m[0].split(".")) words.add(part);
    }
  const thmByLast = new Map<string, string[]>();
  for (const d of decls.values())
    if (inThm(d)) thmByLast.set(last(d.name), [...(thmByLast.get(last(d.name)) ?? []), d.name]);
  const declared = new Set<string>();
  const sourceRoots: string[] = [];
  for (const file of readdirSync(thmDir, { recursive: true, encoding: "utf8" }).filter((f) => f.endsWith(".lean"))) {
    const module = `Tazuna.Thm.${file.replace(/\.lean$/, "").replaceAll("/", ".")}`;
    const code = readFileSync(join(thmDir, file), "utf8")
      .replace(/\/-[\s\S]*?-\//g, (c) => c.replace(/[^\n]/g, " "))
      .replace(/--.*$/gm, "");
    const namespaces: string[] = [];
    const chunks: { owner: string | undefined; text: string }[] = [];
    let mutual: string[] | undefined;
    for (const line of code.split("\n")) {
      if (line !== "" && !/^\s/.test(line)) {
        let owner: string | undefined;
        if (/^mutual\b/.test(line)) mutual = [];
        if (/^end\s*$/.test(line) && mutual) {
          for (const a of mutual) for (const b of mutual) if (a !== b) decls.get(a)?.uses.push(b);
          mutual = undefined;
        }
        const ns = line.match(/^namespace (\S+)/);
        if (ns) namespaces.push(ns[1] ?? "");
        const end = line.match(/^end (\S+)/);
        if (end && namespaces.at(-1) === end[1]) namespaces.pop();
        const m = line.match(declRe);
        if (m) {
          owner = [...namespaces, m[2] ?? ""].join(".");
          declared.add(`${module} ${last(m[2] ?? "")}`);
          if (!decls.has(owner)) owner = "";
          else {
            mutual?.push(owner);
            if (/^@\[[^\]]*\bsimp\b/.test(line)) sourceRoots.push(owner);
          }
        }
        chunks.push({ owner, text: line });
      } else {
        const c = chunks.at(-1);
        if (c) c.text += `\n${line}`;
      }
    }
    for (const { owner, text } of chunks) {
      if (owner === "") continue;
      const tokens =
        owner === undefined
          ? [...text.matchAll(/[A-Za-z_][\w.'?!]*/g)].map((t) => t[0])
          : [
              ...text.matchAll(/\b(?:simp|dsimp|simp_all|simpa|simp_arith|agree|unfold|delta)\b[^[\n]*\[([^\]]*)\]/g),
            ].flatMap((m) => [...(m[1] ?? "").matchAll(/[A-Za-z_][\w.'?!]*/g)].map((t) => t[0]));
      for (const token of tokens)
        for (const target of thmByLast.get(last(token)) ?? []) {
          if (token.includes(".") && !`.${target}`.endsWith(`.${token}`)) continue;
          if (owner === undefined) sourceRoots.push(target);
          else if (target !== owner) decls.get(owner)?.uses.push(target);
        }
    }
  }
  const reached = new Set<string>();
  const stack = [
    ...[...decls.values()].filter((d) => !inThm(d) || words.has(d.name) || words.has(last(d.name))).map((d) => d.name),
    ...sourceRoots,
  ];
  for (let name = stack.pop(); name !== undefined; name = stack.pop()) {
    if (reached.has(name)) continue;
    reached.add(name);
    for (const u of decls.get(name)?.uses ?? []) if (!reached.has(u)) stack.push(u);
  }
  return [...decls.values()]
    .filter((d) => inThm(d) && !reached.has(d.name) && declared.has(`${d.module} ${last(d.name)}`))
    .map((d) => `${d.module} ${d.name}`)
    .toSorted();
}

test("Every declaration of lean/Tazuna/Thm backs a cited property: docs, code, or another reached declaration reaches it", () => {
  assert.deepEqual(unreached(graph()), []);
});
