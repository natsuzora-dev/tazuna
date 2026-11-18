import { type ChildProcess, execFileSync, spawn } from "node:child_process";
import { closeSync, mkdtempSync, openSync, readSync, rmSync, writeSync } from "node:fs";
import { tmpdir } from "node:os";
import { join } from "node:path";
import { StringDecoder } from "node:string_decoder";
import type { Mismatch } from "../../src/data/mismatch.generated.ts";
import type { Scenario } from "../../src/data/scenario.generated.ts";
import type { TraceLine } from "../../src/data/trace.generated.ts";
import { type FileLine, isMalformed } from "../../src/data/trace.ts";
import type { Uncomparable } from "../../src/data/uncomparable.generated.ts";
import type { Json } from "../../src/data/values.ts";
import type { Spec } from "../../src/load/load.ts";
import type { StepOrder } from "../../src/sim/network.ts";
import type { Structure } from "../../src/spec/structure.generated.ts";
import type { Answering, ReadRecord } from "./functions.ts";
import type { Asked, Reply, Request, Response } from "./protocol.generated.ts";

const executable = join(import.meta.dirname, "../../lean/.lake/build/bin/tazuna-lean");

// No signal listeners: the tests talk to Lean synchronously, so a listener would not run until the synchronous work
// ends, and the process would stop exiting on signals.
const running = new Set<ChildProcess>();
process.once("exit", () => {
  for (const child of running) child.kill();
});

export type VerifyViolation = Mismatch | Uncomparable;

/** The response that each request gets. */
const responses = {
  check: "checked",
  verify: "verified",
  checkExternal: "checkedExternal",
  pair: "paired",
  pairSnapshots: "pairedSnapshots",
  compareSnapshot: "comparedSnapshot",
  afters: "afters",
  decodeLines: "decodedLines",
  simulate: "simulated",
  stepOrderChanges: "stepOrderChanges",
} as const satisfies Record<Request["type"], Response["type"]>;

type Responded<T extends Request["type"]> = Omit<Extract<Response, { type: (typeof responses)[T] }>, "type">;

const fileLines = (lines: readonly FileLine[]) =>
  lines.map((l) => (l === undefined ? null : isMalformed(l) ? "malformed" : l));

/**
 * The tazuna-lean process. The spec functions are called synchronously and read records midway, so talking to Lean
 * must be synchronous too: stdin and stdout go through two named pipes, and readSync waits for each answer.
 */
export class Lean {
  private readonly dir: string;
  private readonly toLean: number;
  private readonly fromLean: number;
  private readonly child: ChildProcess;
  /** The received text after the last line taken. */
  private buffered = "";
  /** The earlier chunks of a line that has not ended yet. */
  private parts: string[] = [];
  private readonly decoder = new StringDecoder("utf8");
  private readonly chunk = Buffer.alloc(65536);

  constructor() {
    this.dir = mkdtempSync(join(tmpdir(), "tazuna-lean-"));
    const [input, output] = [join(this.dir, "in"), join(this.dir, "out")];
    execFileSync("mkfifo", [input, output]);
    // Opening a FIFO with r+ does not block on the other end. Only this process holds a write end of Lean's input, so
    // when it dies (even by kill -9) Lean reads EOF and exits; once Lean exits, readSync on its output returns 0.
    this.toLean = openSync(input, "r+");
    const leanInput = openSync(input, "r");
    const holder = openSync(output, "r+");
    const leanOutput = openSync(output, "w");
    this.child = spawn(executable, [], { stdio: [leanInput, leanOutput, "inherit"] });
    running.add(this.child);
    this.fromLean = openSync(output, "r");
    for (const fd of [leanInput, leanOutput, holder]) closeSync(fd);
  }

  /**
   * Closes the Lean process. Diff test files call this from after() and register their tests synchronously, after
   * loading specs: awaiting between registrations lets after() close Lean once the earlier tests finish.
   */
  close(): void {
    this.child.kill();
    running.delete(this.child);
    closeSync(this.toLean);
    closeSync(this.fromLean);
    rmSync(this.dir, { recursive: true, force: true });
  }

  private send(message: Request | Reply): void {
    writeSync(this.toLean, `${JSON.stringify(message)}\n`);
  }

  private receive(): Response | Asked {
    for (;;) {
      const end = this.buffered.indexOf("\n");
      if (end >= 0) {
        const line = this.parts.join("") + this.buffered.slice(0, end);
        this.parts = [];
        this.buffered = this.buffered.slice(end + 1);
        return JSON.parse(line) as Response | Asked;
      }
      this.parts.push(this.buffered);
      const n = readSync(this.fromLean, this.chunk);
      if (n === 0) throw new Error("tazuna-lean exited");
      this.buffered = this.decoder.write(this.chunk.subarray(0, n));
    }
  }

  /** Sends `request` and returns Lean's response, answering each question with `functions` meanwhile. */
  private exchange<T extends Request["type"]>(
    request: Extract<Request, { type: T }>,
    functions?: Answering,
  ): Responded<T> {
    this.send(request);
    for (;;) {
      const message = this.receive();
      if (message.type === "error") throw new Error(`tazuna-lean: ${message.message}`);
      if (message.type === responses[request.type as T]) {
        const { type: _, ...response } = message;
        return response as unknown as Responded<T>;
      }
      if (functions === undefined) throw new Error(`tazuna-lean asked ${JSON.stringify(message)} for ${request.type}`);
      this.send(functions.answer(message as Asked));
    }
  }

  read(part: Parameters<ReadRecord>[0]): unknown {
    this.send({ type: "read", ...part });
    const served = this.receive();
    if (served.type !== "served") throw new Error(`tazuna-lean answered a read with ${JSON.stringify(served)}`);
    return served.value;
  }

  verify(
    spec: Spec,
    service: string,
    snapshot: readonly (TraceLine | undefined)[],
    trace: readonly FileLine[],
    functions: Answering,
  ): Responded<"verify"> {
    const lines = { snapshot: snapshot.map((l) => l ?? null), trace: fileLines(trace) };
    return this.exchange({ type: "verify", structure: spec.structure, service, ...lines }, functions);
  }

  checkExternal(spec: Spec, service: string, trace: readonly FileLine[]): Responded<"checkExternal">["findings"] {
    return this.exchange({ type: "checkExternal", structure: spec.structure, service, trace: fileLines(trace) })
      .findings;
  }

  afters(snapshot: readonly (TraceLine | undefined)[]): Responded<"afters">["findings"] {
    return this.exchange({ type: "afters", snapshot: snapshot.map((l) => l ?? null) }).findings;
  }

  decodeLines(values: readonly Json[]): Responded<"decodeLines">["lines"] {
    return this.exchange({ type: "decodeLines", values }).lines;
  }

  pair(request: Omit<Extract<Request, { type: "pair" }>, "type">): Responded<"pair"> {
    return this.exchange({ type: "pair", ...request });
  }

  pairSnapshots(request: Omit<Extract<Request, { type: "pairSnapshots" }>, "type">): Responded<"pairSnapshots"> {
    return this.exchange({ type: "pairSnapshots", ...request });
  }

  compareSnapshot(
    snapshot: readonly (Json | undefined)[],
    run: readonly Json[],
  ): Responded<"compareSnapshot">["mismatch"] {
    return this.exchange({ type: "compareSnapshot", snapshot: snapshot.map((l) => l ?? null), run }).mismatch;
  }

  /** Lean's stepOrderChanges of the scenario executed from its startup: each search, what it ran, and what it found. */
  stepOrderChanges(spec: Spec, scenario: Scenario, functions: Answering): Responded<"stepOrderChanges">["searched"] {
    return this.exchange({ type: "stepOrderChanges", structure: spec.structure, scenario }, functions).searched;
  }

  /** Simulates the scenario, or with `execute` runs its lines as explore does and returns what each service enables. */
  simulate(
    spec: Spec,
    scenario: Scenario,
    functions: Answering,
    execute = false,
    stepOrders: readonly StepOrder[] = [],
  ): Responded<"simulate"> {
    return this.exchange(
      {
        type: "simulate",
        structure: spec.structure,
        scenario,
        ...(execute ? { execute } : {}),
        ...(stepOrders.length > 0 ? { stepOrders } : {}),
      },
      functions,
    );
  }

  check(structure: Structure): Responded<"check">["findings"] {
    return this.exchange({ type: "check", structure }).findings;
  }
}
