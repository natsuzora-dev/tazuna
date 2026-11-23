import { statSync } from "node:fs";
import { join, relative, resolve } from "node:path";
import { checkSpecWith, failureText } from "../check/spec.ts";
import { type TypeCheck, typeCheck } from "../check/typeCheck.ts";
import type { Converter } from "../convert/program.ts";
import type { ReportedViolation, ViolationValue } from "../data/violation.ts";
import { comparePlaces, placeOf, reportedOfFound } from "../load/found.ts";
import type { Spec } from "../load/load.ts";
import { verifyTraces } from "../verify/index.ts";
import { explain } from "./explain.ts";
import { testSpec } from "./test.ts";
import { isViewerBuilt, viewerFolder, viewSpec } from "./view.ts";

interface Io {
  /** The base of relative spec and trace paths, and of the paths in the printed violation lines. */
  readonly cwd: string;
  readonly log: (line: string) => void;
  readonly error: (line: string) => void;
  /** The built viewer folder; defaults to viewerFolder. */
  readonly viewer?: string;
  readonly typeCheck?: (specRoot: string, cwd: string) => TypeCheck;
  /** The converter of spec functions to share across commands; without one, each command runs its own. */
  readonly converter?: Converter;
}

/** A command's arguments, parsed before the spec is checked. */
type Invocation =
  | { readonly command: "check"; readonly root: string }
  | {
      readonly command: "test";
      readonly root: string;
      readonly update: boolean;
      /** The `<service>/<scenario>` names that --only selects; empty to run every scenario. */
      readonly only: readonly string[];
    }
  | { readonly command: "verify"; readonly root: string; readonly traces: string; readonly coverage: boolean }
  | { readonly command: "view"; readonly root: string; readonly port: number; readonly viewer: string }
  | { readonly command: "explain"; readonly markdown: string };

type Name = Invocation["command"];

/** A usage error; `help` adds the hint to run tazuna --help. */
interface Misuse {
  readonly misuse: string;
  readonly help?: true;
}

/** An option: a flag, an option with one `value`, or a `repeatable` one that collects every value. */
type Option =
  | { readonly kind: "flag"; readonly description: string }
  | { readonly kind: "single"; readonly value: string; readonly description: string }
  | { readonly kind: "repeatable"; readonly value: string; readonly description: string };

/** The parsed value of each option of `O`: whether a flag was given, the value, or every value in order. */
type Parsed<O extends Readonly<Record<string, Option>>> = {
  readonly [K in keyof O]: O[K] extends { readonly kind: "flag" }
    ? boolean
    : O[K] extends { readonly kind: "repeatable" }
      ? readonly string[]
      : string | undefined;
};

interface Command<O extends Readonly<Record<string, Option>>> {
  /** Whether the first argument is the spec folder, which must exist. */
  readonly spec: boolean;
  /** The arguments after the spec folder. */
  readonly positionals: readonly string[];
  readonly description: string;
  readonly options: O;
  /** Parses what the table's arity and option checks let through. `root` is the spec folder, or "" without one. */
  readonly parse: (
    given: { readonly root: string; readonly positionals: readonly string[]; readonly options: Parsed<O> },
    io: Io,
  ) => Invocation | Misuse;
}

type ParsedValue = boolean | string | readonly string[] | undefined;

/** A command whose option values parse fills in by the kinds of its options. */
type AnyCommand = Omit<Command<Readonly<Record<string, Option>>>, "parse"> & {
  readonly parse: (
    given: {
      readonly root: string;
      readonly positionals: readonly string[];
      readonly options: Readonly<Record<string, ParsedValue>>;
    },
    io: Io,
  ) => Invocation | Misuse;
};

const command = <const O extends Readonly<Record<string, Option>>>(c: Command<O>): AnyCommand => ({
  ...c,
  parse: (given, io) => c.parse({ ...given, options: given.options as Parsed<O> }, io),
});

const isFolder = (path: string) => statSync(path, { throwIfNoEntry: false })?.isDirectory() === true;

const commands = {
  check: command({
    spec: true,
    positionals: [],
    description: "Check the spec's structure and source without running it.",
    options: {},
    parse: ({ root }) => ({ command: "check", root }),
  }),
  test: command({
    spec: true,
    positionals: [],
    description:
      "Simulate every scenario, explore the paths after it within the bounds of its service's explore(), and search the step orders that no line writes: the steps of one message that no cause chain links, and the messages that one line delivers to one service, equal messages included. A move is one act that faces the own service, with the network lines that it needs, such as a client request, or an external peer's answer with the lines that deliver the request and the answer. test reports each violation once per kind, definition, data, and location, from the first path that reports it, taking the scenarios in order and each scenario's paths breadth-first. A violation that only an explored path reports lists the path's lines after the scenario in its appendedLines field. When a scenario's run does not halt, test compares the trace of each running service with its snapshot: <service>/__snapshots__/<scenario>.jsonl for the own service, and <service>/__snapshots__/<scenario>.<peer>.jsonl for each running peer that has lines. A scenario whose run did not halt and has no snapshot, a snapshot without a scenario, and any other entry of __snapshots__ are violations.",
    options: {
      "--update": {
        kind: "flag",
        description:
          "Write the snapshot of each scenario whose run did not halt instead of comparing the run with it, and remove the snapshots without a scenario.",
      },
      "--only": {
        kind: "repeatable",
        value: "service/scenario",
        description:
          "Run only the scenario named exactly <service>/<scenario>, the service and name fields of a violation's scenario. The snapshots of the scenarios that do not run, and the other entries named after them, are neither compared, reported, nor removed.",
      },
    },
    parse: ({ root, options }) => {
      const { "--update": update, "--only": only } = options;
      return { command: "test", root, update, only };
    },
  }),
  verify: command({
    spec: true,
    positionals: ["traces"],
    description:
      'Check traces of implementations against the spec. Each file under <traces>/<service>, at any depth and with any name, is a trace of the implementation of the service <service>: its trace lines, after a first line {"type":"start","time","records"} that states the time and the records that the implementation starts from. A trace without that line starts from no records at the time of its first line. For a spec service, verify replays the trace: the spec takes the trace\'s in lines in order, each at its time, with the values that the implementation stands for in its own way (its keys, its request ids) bound to the spec\'s by the out lines so far, and then verify compares the trace\'s lines with the spec\'s, and reports what the spec reports while it takes them. verify checks a trace of an external service against the service\'s contract once the trace ends, so a result event may come before or after its request\'s answer. Any other entry of <traces> is a violation.',
    options: {
      "--coverage": {
        kind: "flag",
        description:
          "Also report the parts of commands, queries, automations, and charts that no trace's replay reaches (Uncovered).",
      },
    },
    parse: ({ root, positionals: [traces = ""], options }, io) =>
      isFolder(resolve(io.cwd, traces))
        ? { command: "verify", root, traces: resolve(io.cwd, traces), coverage: options["--coverage"] }
        : { misuse: `no such folder ${traces}` },
  }),
  view: command({
    spec: true,
    positionals: [],
    description:
      "Serve the viewer of the spec's services, definitions, and scenario snapshots, and print its URL. The viewer reloads when a spec file or snapshot changes.",
    options: { "--port": { kind: "single", value: "n", description: "Serve on port n instead of a free port." } },
    parse: ({ root, options }, io) => {
      const port = options["--port"] ?? "0";
      if (!/^\d+$/.test(port) || Number(port) > 65535)
        return { misuse: `invalid port ${port} (expected an integer from 0 to 65535)` };
      const viewer = io.viewer ?? viewerFolder;
      if (!isViewerBuilt(viewer)) return { misuse: "viewer not built. Run npm run build -w tazuna" };
      return { command: "view", root, port: Number(port), viewer };
    },
  }),
  explain: command({
    spec: false,
    positionals: ["kind"],
    description:
      "Print in markdown what the violation kind <kind>, such as Fault.failedEnsures, means, who reports it, and the side at fault, and, when tazuna's tests have one, an example: the top-level statement of a spec that holds the reported line, with that line marked, and the violation line that tazuna reports on it.",
    options: {},
    parse: ({ positionals: [kind = ""] }) => {
      const explained = explain(kind);
      return "misuse" in explained ? explained : { command: "explain", markdown: explained.markdown };
    },
  }),
} satisfies { readonly [N in Name]: AnyCommand };

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

const usageOf = (o: Option) => {
  switch (o.kind) {
    case "flag":
      return "";
    case "single":
      return ` <${o.value}>`;
    case "repeatable":
      return ` <${o.value}> (repeatable)`;
  }
};

const help = [
  "Usage: tazuna <command> [arguments] [options]",
  "",
  "Commands:",
  ...Object.entries(commands).flatMap(([name, c]) => [
    ...entry(
      "  ",
      [name, ...(c.spec ? ["spec"] : []), ...c.positionals].map((a, i) => (i === 0 ? a : `<${a}>`)).join(" "),
      c.description,
    ),
    ...Object.entries<Option>(c.options).flatMap(([option, o]) =>
      entry("    ", `${option}${usageOf(o)}`, o.description),
    ),
  ]),
  "",
  "Options:",
  ...entry("  ", "-h, --help", "Print this help."),
  "",
  ...wrap(
    "",
    "A violation after which the spec's behavior is undefined, or a line that cannot take place, halts the run. test then neither writes nor compares that scenario's snapshot, and test --update leaves an existing snapshot of that scenario as it is; verify's replay takes no more in lines. test compares nothing with a snapshot that has a line that the trace line schema cannot read or an after field that names no earlier out line since the input line before it. verify stops at the first line of a trace that the trace line schema cannot read and reports that line. It compares no line after the last in line before that line, and checks no line of an external service's trace after that line. Blank lines of traces and snapshots are skipped, and line numbers count them.",
  ),
  "",
  ...wrap(
    "",
    "<spec> is the folder whose .ts files hold the spec, in any subfolders except __snapshots__ and node_modules, without .d.ts files. A symlinked folder is walked once. Every command but explain first checks the spec as check does, and does nothing else when that reports a violation. check runs tsc --noEmit, from the typescript package that <spec> resolves, on the nearest tsconfig.json at or above <spec>, writes tsc's output to stderr, and stops if tsc reports an error. A spec file outside tsc's program is Malformed. If loading the spec finds a Malformed violation, check reports the violations that loading finds (Malformed, NonCanonical, Restricted) without checking the spec's structure (Illegal). No tsconfig.json at or above <spec>, no typescript package that <spec> resolves, a tsc that does not finish, or a spec file that throws when imported is a usage error. tazuna reports the last in one line with the error and the first place outside node: in its stack. Unless tsc reports an error or a usage error stops them, check, test, and verify write to stdout one JSON line per violation, whose location.file is relative to the current directory, and write to stderr one summary line, <what was checked>: <number of violations, or no violations>, where test's <what was checked> is how many scenarios it ran out of all, and the paths of the snapshots that test --update writes or removes.",
  ),
  ...wrap(
    "",
    "The exit code is 1 when tsc reports an error or a command reports a violation, 2 on a usage error, and 0 otherwise.",
  ),
].join("\n");

/** The parts that `verify --coverage` reports, each at its definition, in place order. */
const uncoveredOf = (spec: Spec, uncovered: readonly ViolationValue[]): ReportedViolation[] =>
  uncovered
    .map((violation) => ({ violation, place: placeOf(spec, violation.definition) }))
    .sort((x, y) => comparePlaces(x.place, y.place))
    .map(reportedOfFound);

const count = (n: number, noun: string) => `${n} ${noun}${n === 1 ? "" : "s"}`;

function record(io: Io, specRoot: string, r: ReportedViolation): string {
  return JSON.stringify({ ...r, location: { ...r.location, file: relative(io.cwd, join(specRoot, r.location.file)) } });
}

/**
 * Writes the violation lines to stdout, and to stderr the summary `<subject>: <result>`, such as `3 files: no violations`.
 */
function report(io: Io, specRoot: string, violations: readonly ReportedViolation[], subject: string): number {
  for (const p of violations) io.log(record(io, specRoot, p));
  io.error(`${subject}: ${violations.length === 0 ? "no violations" : count(violations.length, "violation")}`);
  return violations.length === 0 ? 0 : 1;
}

const isName = (command: string): command is Name => Object.hasOwn(commands, command);

/** Parses `args` by the command table, before anything reads the spec. */
function parse(args: readonly string[], io: Io): Invocation | Misuse {
  const [name = "", ...rest] = args;
  if (!isName(name)) return { misuse: `unknown command ${name}`, help: true };
  const known = commands[name];
  const options: Record<string, ParsedValue> = {};
  for (const [option, o] of Object.entries(known.options))
    if (o.kind !== "single") options[option] = o.kind === "flag" ? false : [];
  const positionals: string[] = [];
  const given = new Set<string>();
  for (let i = 0; i < rest.length; i += 1) {
    const arg = rest[i] ?? "";
    const option = known.options[arg];
    if (!arg.startsWith("-")) {
      positionals.push(arg);
      continue;
    }
    if (option === undefined) return { misuse: `unknown option ${arg} for ${name}`, help: true };
    if (option.kind !== "repeatable" && given.has(arg)) return { misuse: `${arg} given twice`, help: true };
    given.add(arg);
    if (option.kind === "flag") {
      options[arg] = true;
      continue;
    }
    const value = rest[i + 1];
    if (value === undefined || value.startsWith("-")) return { misuse: `missing value for ${arg}`, help: true };
    const values = options[arg];
    options[arg] = Array.isArray(values) ? [...values, value] : value;
    i += 1;
  }
  const arity = known.positionals.length + (known.spec ? 1 : 0);
  if (positionals.length !== arity) return { misuse: `wrong number of arguments for ${name}`, help: true };
  const [root = "", ...after] = known.spec ? positionals : ["", ...positionals];
  if (known.spec && !isFolder(resolve(io.cwd, root))) return { misuse: `no such folder ${root}` };
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
  if (invocation.command === "explain") {
    io.log(invocation.markdown);
    return 0;
  }
  const { root } = invocation;
  const specRoot = resolve(io.cwd, root);
  const result = await checkSpecWith(specRoot, (io.typeCheck ?? typeCheck)(specRoot, io.cwd), io.converter);
  if (result.kind === "typeErrors") {
    io.error(failureText(result, root));
    return 1;
  }
  if (result.kind !== "violations" && result.kind !== "checked") return misused(failureText(result, root));
  if (result.kind === "violations" || invocation.command === "check") {
    const files = result.kind === "violations" ? result.files : result.spec.sources.length;
    const violations = result.kind === "violations" ? result.violations : [];
    return report(io, specRoot, violations, count(files, "file"));
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
      const { only } = invocation;
      const nameOf = (s: { readonly service: string; readonly name: string }) => `${s.service}/${s.name}`;
      const unknown = only.find((name) => !spec.scenarios.some((s) => nameOf(s) === name));
      if (unknown !== undefined) return misused(`unknown scenario ${unknown}`);
      const scenarios = only.length === 0 ? spec.scenarios : spec.scenarios.filter((s) => only.includes(nameOf(s)));
      const tested = testSpec(spec, { update: invocation.update, scenarios });
      for (const written of tested.written) io.error(`Updated 1 snapshot: ${join(root, relative(spec.root, written))}`);
      for (const removed of tested.removed) io.error(`Removed 1 snapshot: ${join(root, relative(spec.root, removed))}`);
      const ran = `${scenarios.length}/${spec.scenarios.length} scenarios${only.length === 0 ? "" : " (--only)"}`;
      return report(io, spec.root, tested.violations, ran);
    }
    case "verify": {
      const verified = verifyTraces(spec, invocation.traces);
      const violations = [
        ...(invocation.coverage ? uncoveredOf(spec, verified.uncovered) : []),
        ...verified.violations,
      ];
      return report(io, spec.root, violations, count(verified.traces, "trace"));
    }
  }
}
