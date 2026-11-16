import { statSync } from "node:fs";
import { join, relative, resolve } from "node:path";
import type { Problem } from "../data/problem.ts";
import { loadSpec } from "../load/load.ts";
import { verifyTraces } from "../verify/index.ts";
import { check } from "./check.ts";
import { testSpec, uncoveredOf } from "./test.ts";
import { type TypeCheck, typeCheck } from "./typeCheck.ts";
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

interface Command {
  readonly positionals: readonly string[];
  readonly description: string;
  /** An option with `value` takes the next argument. */
  readonly options: Readonly<
    Record<string, { readonly value?: string; readonly required?: true; readonly description: string }>
  >;
}

const commands: Readonly<Record<string, Command>> = {
  check: {
    positionals: ["spec"],
    description: "Check the spec's structure and source without running it.",
    options: {},
  },
  test: {
    positionals: ["spec"],
    description:
      "Run the checks of check first; if they report a violation, report those violations and run no scenario. Otherwise run every scenario and the paths that --depth appends to it, report the violations found on every path, and compare the trace of each scenario whose run did not halt with its snapshot (<service>/__snapshots__/<scenario>.jsonl). For each other spec service <peer> that the scenario sends a request to, receives an event from, or names in given, elsewhere or from, test runs <peer>'s spec on the inputs that it derives from the scenario, reports the scenario's answers, events and requests of <peer> that this run does not give, and compares the run, unless it halted or took no input, with the snapshot <service>/__snapshots__/<scenario>.<peer>.jsonl. test reports a violation once per kind, definition, data, and the location that the violation itself names, from the first path that reports it, taking the scenarios in order and each scenario's paths breadth-first; a deadlineOrder, answerOrder, or stepOrder violation counts as the same violation whichever of its two sides comes first. A violation that only a path with appended inputs reports lists those inputs in its appendedInputs field, as trace-shaped steps. A scenario whose run did not halt and has no snapshot, a snapshot without a scenario, and any other entry of __snapshots__ are violations.",
    options: {
      "--depth": {
        value: "n",
        required: true,
        description:
          "Append up to n inputs to each scenario. test compares the two orders of a pair of appended inputs only on paths of at most n - 2 appended inputs, because each order appends both inputs.",
      },
      "--update": {
        description:
          "Write the snapshot of each scenario whose run did not halt instead of comparing the run with it, and remove the snapshots without a scenario.",
      },
      "--coverage": {
        description:
          "Also report the parts of commands, queries, automations, and charts that neither a scenario's run nor a path that --depth appends reaches (Uncovered).",
      },
    },
  },
  verify: {
    positionals: ["spec", "traces"],
    description:
      "Compare implementation traces with the snapshots without running the spec. <traces> is a folder of <service>/<scenario>.jsonl traces, and of <service>/<scenario>.<peer>.jsonl traces of the implementation of another spec service <peer> on the inputs that test derives from the scenario, which verify compares with the snapshot <service>/__snapshots__/<scenario>.<peer>.jsonl as <peer>'s trace; any other entry of it is a violation. verify checks a trace of an external service against the service's contract. verify also reports traces that name no scenario and snapshots without a trace, and skips a trace that has no snapshot.",
    options: {},
  },
  view: {
    positionals: ["spec"],
    description:
      "Serve the viewer of the spec's services, definitions, and scenario snapshots, and print its URL. The viewer reloads when a spec file or snapshot changes.",
    options: { "--port": { value: "n", description: "Serve on port n instead of a free port." } },
  },
};

const entry = (indent: string, usage: string, description: string) => [
  `${indent}${usage}`,
  `${indent}    ${description}`,
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
  `A violation after which the spec's behavior is undefined, or an error in a scenario input that no trace line can
record, stops the run: test neither writes nor compares that scenario's snapshot. test --update leaves an existing
snapshot of that scenario as it is, and verify still compares traces with it. test and verify compare nothing with a
snapshot that has a line that the trace line schema cannot read or an after field that names no earlier out line of
its window. verify compares no line of a trace after an input line that differs from the snapshot's. Unless such an input
line stops the comparison first, verify stops at the first line of a trace that the trace line schema cannot read and
reports that line: it compares no line after the last input line before that line, and checks no line of an external
service's trace after that line. Blank lines of traces and snapshots are skipped, and line numbers count them.

<spec> is a folder whose direct subfolders are services. check and test first run tsc --noEmit, from the typescript
package that <spec> resolves, on the nearest tsconfig.json at or above <spec>, which must include the spec's files,
and write tsc's output to stderr. If tsc reports an error, check and test stop without checking the spec. If loading
the spec finds a Malformed violation, check and test report the violations that loading finds (Malformed,
NonCanonical, Restricted) and stop without checking the spec's structure (Illegal). No tsconfig.json at or above <spec>, no typescript package
that <spec> resolves, or a tsc that does not finish, is a usage error. Unless tsc reports an error or a usage error
stops them, check, test, and verify write to stdout one JSON line per violation, whose location.file is relative to the
current directory, and write to stderr the number of violations, or that they found none, and the paths of the
snapshots that test --update writes or removes.
The exit code is 1 when tsc reports an error or a command reports a violation, 2 on a usage error, and 0 otherwise.`,
].join("\n");

const isFolder = (path: string) => statSync(path, { throwIfNoEntry: false })?.isDirectory() === true;

const count = (n: number, noun: string) => `${n} ${noun}${n === 1 ? "" : "s"}`;

function record(io: Io, specRoot: string, r: Problem): string {
  return JSON.stringify({ ...r, location: { ...r.location, file: relative(io.cwd, join(specRoot, r.location.file)) } });
}

function report(io: Io, specRoot: string, problems: readonly Problem[], done: string): number {
  for (const p of problems) io.log(record(io, specRoot, p));
  io.error(`${done}. ${problems.length === 0 ? "No problems found" : count(problems.length, "problem")}.`);
  return problems.length === 0 ? 0 : 1;
}

export async function main(args: readonly string[], io: Io): Promise<number> {
  if (args.length === 0 || args.includes("--help") || args.includes("-h")) {
    io.log(help);
    return 0;
  }
  const [command = "", ...rest] = args;
  const misused = (message: string) => {
    io.error(`tazuna: ${message}.`);
    return 2;
  };
  const usage = (message: string) => misused(`${message}. Run tazuna --help for usage`);
  const known = commands[command];
  if (known === undefined) return usage(`unknown command ${command}`);
  const options = new Map<string, string>();
  const positional: string[] = [];
  for (let i = 0; i < rest.length; i += 1) {
    const arg = rest[i] ?? "";
    const value = rest[i + 1];
    if (!arg.startsWith("-")) positional.push(arg);
    else if (known.options[arg] === undefined) return usage(`unknown option ${arg} for ${command}`);
    else if (known.options[arg].value === undefined) options.set(arg, "");
    else if (value === undefined || value.startsWith("-")) return usage(`missing value for ${arg}`);
    else {
      options.set(arg, value);
      i += 1;
    }
  }
  if (positional.length !== known.positionals.length) return usage(`wrong number of arguments for ${command}`);
  const missing = Object.keys(known.options).find((o) => known.options[o]?.required === true && !options.has(o));
  if (missing !== undefined) return usage(`missing option ${missing} for ${command}`);
  const [target, traceFolder] = positional;
  const root = target ?? "";
  if (!isFolder(resolve(io.cwd, root))) return misused(`no such folder ${root}`);
  if (command === "view") {
    const given = options.get("--port") ?? "0";
    const port = Number(given);
    if (!/^\d+$/.test(given) || port > 65535)
      return misused(`invalid port ${given} (expected an integer from 0 to 65535)`);
    const folder = io.viewer ?? viewerFolder;
    if (!isViewerBuilt(folder)) return misused("viewer not built. Run npm run build -w tazuna");
    const server = await viewSpec({ root: resolve(io.cwd, root), path: root }, port, folder);
    if (server === undefined) return misused(`port ${port} in use`);
    io.log(`Serving the viewer at ${server.url}`);
    await server.closed;
    return 0;
  }
  const givenDepth = options.get("--depth");
  if (givenDepth !== undefined && !/^\d+$/.test(givenDepth))
    return misused(`invalid depth ${givenDepth} (expected a non-negative integer)`);
  if (command === "check" || command === "test") {
    const typeChecked = (io.typeCheck ?? typeCheck)(resolve(io.cwd, root), io.cwd);
    if (typeChecked.kind === "noTsconfig") return misused(`no tsconfig.json at or above ${root}`);
    if (typeChecked.kind === "noTypescript") return misused(`cannot resolve typescript from ${root}`);
    if (typeChecked.kind === "unfinished") return misused(`tsc did not finish: ${typeChecked.reason}`);
    if (typeChecked.output !== "") io.error(typeChecked.output.trimEnd());
    if (!typeChecked.passed) return 1;
  }
  const spec = await loadSpec(resolve(io.cwd, root));
  const checked = `Checked ${count(spec.sources.length, "file")}`;
  if (command === "check") return report(io, spec.root, check(spec), checked);
  if (command === "test") {
    const depth = Number(givenDepth);
    const failed = check(spec);
    if (failed.length > 0) return report(io, spec.root, failed, checked);
    const result = testSpec(spec, { update: options.has("--update"), depth });
    for (const written of result.written) io.error(`Updated 1 snapshot: ${join(root, relative(spec.root, written))}`);
    for (const removed of result.removed) io.error(`Removed 1 snapshot: ${join(root, relative(spec.root, removed))}`);
    const problems = [...(options.has("--coverage") ? uncoveredOf(spec, result.reached) : []), ...result.problems];
    const paths = `the paths that append up to ${count(depth, "input")}`;
    return report(io, spec.root, problems, `Tested ${count(spec.scenarios.length, "scenario")} and ${paths}`);
  }
  const traces = resolve(io.cwd, traceFolder ?? "");
  if (!isFolder(traces)) return misused(`no such folder ${traceFolder}`);
  const result = verifyTraces(spec, traces);
  return report(io, spec.root, result.problems, `Verified ${count(result.traces, "trace")}`);
}
