import { statSync } from "node:fs";
import { join, relative, resolve } from "node:path";
import { checkSpecWith, failureText } from "../check/spec.ts";
import { type TypeCheck, typeCheck } from "../check/typeCheck.ts";
import type { ReportedViolation } from "../data/violation.ts";
import { verifyTraces } from "../verify/index.ts";
import { testSpec, uncoveredOf } from "./test.ts";
import { isViewerBuilt, viewerFolder, viewSpec } from "./view.ts";

interface Io {
  /** The base of relative spec and trace paths, and of the paths in the printed violation lines. */
  readonly cwd: string;
  readonly log: (line: string) => void;
  readonly error: (line: string) => void;
  /** The built viewer folder; defaults to viewerFolder. */
  readonly viewer?: string;
  readonly typeCheck?: (specRoot: string, cwd: string) => TypeCheck;
}

/** A command's arguments, parsed before the spec is checked. */
type Invocation =
  | { readonly command: "check"; readonly root: string }
  | {
      readonly command: "test";
      readonly root: string;
      readonly depth: number;
      readonly update: boolean;
      readonly coverage: boolean;
    }
  | { readonly command: "verify"; readonly root: string; readonly traces: string }
  | { readonly command: "view"; readonly root: string; readonly port: number; readonly viewer: string };

type Name = Invocation["command"];

/** A usage error; `help` adds the hint to run tazuna --help. */
interface Misuse {
  readonly misuse: string;
  readonly help?: true;
}

interface Given {
  readonly root: string;
  /** The arguments after the spec root. */
  readonly positionals: readonly string[];
  /** The value of each given option, or "" for an option without a value. */
  readonly options: ReadonlyMap<string, string>;
}

interface Command<N extends Name> {
  readonly positionals: readonly string[];
  readonly description: string;
  /** An option with `value` takes the next argument. */
  readonly options: Readonly<
    Record<string, { readonly value?: string; readonly required?: true; readonly description: string }>
  >;
  /** Parses what the table's arity and option checks let through. */
  readonly parse: (given: Given, io: Io) => Extract<Invocation, { readonly command: N }> | Misuse;
}

const isFolder = (path: string) => statSync(path, { throwIfNoEntry: false })?.isDirectory() === true;

const commands: { readonly [N in Name]: Command<N> } = {
  check: {
    positionals: ["spec"],
    description: "Check the spec's structure and source without running it.",
    options: {},
    parse: ({ root }) => ({ command: "check", root }),
  },
  test: {
    positionals: ["spec"],
    description:
      "Simulate every scenario, explore the paths of up to --depth moves after it, and search the orders of the steps of each message that no cause orders and of the messages that one line delivers to one service, equal messages included. Report the violations of every path once per kind, definition, data and location, from the first path that reports it, taking the scenarios in order and each scenario's paths breadth-first; a stepOrder violation counts as the same violation whichever of its two steps comes first, and a violation that only an explored path reports lists the path's lines after the scenario in its appendedLines field. Compare the trace of each running service of a scenario that did not halt with its snapshot: the own service's <service>/__snapshots__/<scenario>.jsonl, and each running peer's with lines <service>/__snapshots__/<scenario>.<peer>.jsonl. A scenario whose run did not halt and has no snapshot, a snapshot without a scenario, and any other entry of __snapshots__ are violations.",
    options: {
      "--depth": {
        value: "n",
        required: true,
        description:
          "Explore paths of up to n moves after each scenario. A move is one act that faces the own service, with the network lines it needs, such as a client request, or an external peer's answer with the lines that deliver the request and the answer.",
      },
      "--update": {
        description:
          "Write the snapshot of each scenario whose run did not halt instead of comparing the run with it, and remove the snapshots without a scenario.",
      },
      "--coverage": {
        description:
          "Also report the parts of commands, queries, automations, and charts that neither a scenario's run nor an explored path reaches (Uncovered).",
      },
    },
    parse: ({ root, options }) => {
      const depth = options.get("--depth") ?? "";
      if (!/^\d+$/.test(depth)) return { misuse: `invalid depth ${depth} (expected a non-negative integer)` };
      const update = options.has("--update");
      return { command: "test", root, depth: Number(depth), update, coverage: options.has("--coverage") };
    },
  },
  verify: {
    positionals: ["spec", "traces"],
    description:
      "Compare implementation traces with the snapshots without running the spec. <traces> is a folder of <service>/<scenario>.jsonl traces, and of <service>/<scenario>.<peer>.jsonl traces of the implementation of another spec service <peer> that runs as a peer in the scenario, which verify compares with the snapshot <service>/__snapshots__/<scenario>.<peer>.jsonl as <peer>'s trace; any other entry of it is a violation. verify checks a trace of an external service against the service's contract once the trace ends, so a result event may come before or after its request's answer. verify also reports traces that name no scenario and snapshots without a trace, and skips a trace that has no snapshot.",
    options: {},
    parse: ({ root, positionals: [traces = ""] }, io) =>
      isFolder(resolve(io.cwd, traces))
        ? { command: "verify", root, traces: resolve(io.cwd, traces) }
        : { misuse: `no such folder ${traces}` },
  },
  view: {
    positionals: ["spec"],
    description:
      "Serve the viewer of the spec's services, definitions, and scenario snapshots, and print its URL. The viewer reloads when a spec file or snapshot changes.",
    options: { "--port": { value: "n", description: "Serve on port n instead of a free port." } },
    parse: ({ root, options }, io) => {
      const port = options.get("--port") ?? "0";
      if (!/^\d+$/.test(port) || Number(port) > 65535)
        return { misuse: `invalid port ${port} (expected an integer from 0 to 65535)` };
      const viewer = io.viewer ?? viewerFolder;
      if (!isViewerBuilt(viewer)) return { misuse: "viewer not built. Run npm run build -w tazuna" };
      return { command: "view", root, port: Number(port), viewer };
    },
  },
};

const helpWidth = 100;

/** Breaks `text` between words into lines of at most helpWidth characters, each starting with `indent`. */
function wrap(indent: string, text: string): string[] {
  const lines: string[] = [];
  let line = "";
  for (const word of text.split(/\s+/)) {
    if (line !== "" && indent.length + line.length + 1 + word.length > helpWidth) {
      lines.push(indent + line);
      line = word;
    } else line = line === "" ? word : `${line} ${word}`;
  }
  return [...lines, indent + line];
}

const entry = (indent: string, usage: string, description: string) => [
  `${indent}${usage}`,
  ...wrap(`${indent}    `, description),
];

const help = [
  "Usage: tazuna <command> [arguments] [options]",
  "",
  "Commands:",
  ...Object.entries(commands).flatMap(([name, c]) => [
    ...entry("  ", `${[name, ...c.positionals.map((a) => `<${a}>`)].join(" ")}`, c.description),
    ...Object.entries(c.options).flatMap(([option, o]) =>
      entry(
        "    ",
        `${option}${o.value === undefined ? "" : ` <${o.value}>`}${o.required === true ? " (required)" : ""}`,
        o.description,
      ),
    ),
  ]),
  "",
  "Options:",
  ...entry("  ", "-h, --help", "Print this help."),
  "",
  ...wrap(
    "",
    "A violation after which the spec's behavior is undefined, or a scenario line that cannot take place, stops the run: test neither writes nor compares that scenario's snapshot. test --update leaves an existing snapshot of that scenario as it is, and verify still compares traces with it. test and verify compare nothing with a snapshot that has a line that the trace line schema cannot read or an after field that names no earlier out line since the input line before it. verify compares no line of a trace after an input line that differs from the snapshot's. Unless such an input line stops the comparison first, verify stops at the first line of a trace that the trace line schema cannot read and reports that line: it compares no line after the last input line before that line, and checks no line of an external service's trace after that line. Blank lines of traces and snapshots are skipped, and line numbers count them.",
  ),
  "",
  ...wrap(
    "",
    "<spec> is the folder whose .ts files hold the spec, in any subfolders except __snapshots__ and node_modules, without .d.ts files; a symlinked folder is walked once. Every command first checks the spec as check does, and does nothing else when that reports a violation. check runs tsc --noEmit, from the typescript package that <spec> resolves, on the nearest tsconfig.json at or above <spec>, writes tsc's output to stderr, and stops if tsc reports an error. A spec file outside tsc's program is Malformed. If loading the spec finds a Malformed violation, check reports the violations that loading finds (Malformed, NonCanonical, Restricted) without checking the spec's structure (Illegal). No tsconfig.json at or above <spec>, no typescript package that <spec> resolves, a tsc that does not finish, or a spec file that throws when imported is a usage error; the last is reported in one line with the error and the first place outside node: in its stack. Unless tsc reports an error or a usage error stops them, check, test, and verify write to stdout one JSON line per violation, whose location.file is relative to the current directory, and write to stderr the number of violations, or that they found none, and the paths of the snapshots that test --update writes or removes.",
  ),
  ...wrap(
    "",
    "The exit code is 1 when tsc reports an error or a command reports a violation, 2 on a usage error, and 0 otherwise.",
  ),
].join("\n");

const count = (n: number, noun: string) => `${n} ${noun}${n === 1 ? "" : "s"}`;

function record(io: Io, specRoot: string, r: ReportedViolation): string {
  return JSON.stringify({ ...r, location: { ...r.location, file: relative(io.cwd, join(specRoot, r.location.file)) } });
}

function report(io: Io, specRoot: string, violations: readonly ReportedViolation[], done: string): number {
  for (const p of violations) io.log(record(io, specRoot, p));
  io.error(`${done}. ${violations.length === 0 ? "No violations found" : count(violations.length, "violation")}.`);
  return violations.length === 0 ? 0 : 1;
}

const isName = (command: string): command is Name => Object.hasOwn(commands, command);

/** Parses `args` by the command table, before anything reads the spec. */
function parse(args: readonly string[], io: Io): Invocation | Misuse {
  const [command = "", ...rest] = args;
  if (!isName(command)) return { misuse: `unknown command ${command}`, help: true };
  const known = commands[command];
  const options = new Map<string, string>();
  const positionals: string[] = [];
  for (let i = 0; i < rest.length; i += 1) {
    const arg = rest[i] ?? "";
    const value = rest[i + 1];
    if (!arg.startsWith("-")) positionals.push(arg);
    else if (known.options[arg] === undefined) return { misuse: `unknown option ${arg} for ${command}`, help: true };
    else if (known.options[arg].value === undefined) options.set(arg, "");
    else if (value === undefined || value.startsWith("-")) return { misuse: `missing value for ${arg}`, help: true };
    else {
      options.set(arg, value);
      i += 1;
    }
  }
  if (positionals.length !== known.positionals.length)
    return { misuse: `wrong number of arguments for ${command}`, help: true };
  const missing = Object.keys(known.options).find((o) => known.options[o]?.required === true && !options.has(o));
  if (missing !== undefined) return { misuse: `missing option ${missing} for ${command}`, help: true };
  const [root = "", ...after] = positionals;
  if (!isFolder(resolve(io.cwd, root))) return { misuse: `no such folder ${root}` };
  return known.parse({ root, positionals: after, options }, io);
}

export async function main(args: readonly string[], io: Io): Promise<number> {
  if (args.length === 0 || args.includes("--help") || args.includes("-h")) {
    io.log(help);
    return 0;
  }
  const misused = (message: string) => {
    io.error(`tazuna: ${message}.`);
    return 2;
  };
  const invocation = parse(args, io);
  if ("misuse" in invocation)
    return misused(invocation.help === true ? `${invocation.misuse}. Run tazuna --help for usage` : invocation.misuse);
  const { root } = invocation;
  const specRoot = resolve(io.cwd, root);
  const result = await checkSpecWith(specRoot, (io.typeCheck ?? typeCheck)(specRoot, io.cwd));
  if (result.kind === "typeErrors") {
    io.error(failureText(result, root));
    return 1;
  }
  if (result.kind !== "violations" && result.kind !== "checked") return misused(failureText(result, root));
  if (result.kind === "violations" || invocation.command === "check") {
    const files = result.kind === "violations" ? result.files : result.spec.sources.length;
    const violations = result.kind === "violations" ? result.violations : [];
    return report(io, specRoot, violations, `Checked ${count(files, "file")}`);
  }
  const { spec } = result;
  switch (invocation.command) {
    case "view": {
      const server = await viewSpec(spec, root, io.cwd, invocation.port, invocation.viewer);
      if (server === undefined) return misused(`port ${invocation.port} in use`);
      io.log(`Serving the viewer at ${server.url}`);
      await server.closed;
      return 0;
    }
    case "test": {
      const { depth } = invocation;
      const tested = testSpec(spec, { update: invocation.update, depth });
      for (const written of tested.written) io.error(`Updated 1 snapshot: ${join(root, relative(spec.root, written))}`);
      for (const removed of tested.removed) io.error(`Removed 1 snapshot: ${join(root, relative(spec.root, removed))}`);
      const violations = [...(invocation.coverage ? uncoveredOf(spec, tested.reached) : []), ...tested.violations];
      const paths = `explored paths of up to ${count(depth, "move")} after each scenario`;
      return report(io, spec.root, violations, `Tested ${count(spec.scenarios.length, "scenario")} and ${paths}`);
    }
    case "verify": {
      const verified = verifyTraces(spec, invocation.traces);
      return report(io, spec.root, verified.violations, `Verified ${count(verified.traces, "trace")}`);
    }
  }
}
