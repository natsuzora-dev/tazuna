import { type ChildProcess, execFileSync, spawn } from "node:child_process";
import { closeSync, mkdtempSync, openSync, readSync, rmSync, writeSync } from "node:fs";
import { tmpdir } from "node:os";
import { join } from "node:path";
import { StringDecoder } from "node:string_decoder";
import type { ChoiceDependent, StepName } from "../../src/data/choiceDependent.generated.ts";
import type { Illegal } from "../../src/data/illegal.generated.ts";
import type { Mismatch } from "../../src/data/mismatch.generated.ts";
import type { Origin, Scenario } from "../../src/data/scenario.generated.ts";
import type { Step } from "../../src/data/step.generated.ts";
import type { TraceLine } from "../../src/data/trace.generated.ts";
import { type FileLine, isMalformed } from "../../src/data/trace.ts";
import type { Uncomparable } from "../../src/data/uncomparable.generated.ts";
import type { Json } from "../../src/data/values.ts";
import type { Spec } from "../../src/load/load.ts";
import type { Enabled } from "../../src/observe/enabled.ts";
import type { Structure } from "../../src/syntax/structure.generated.ts";
import type { Folder, PairingScenario } from "../../src/verify/pairing.ts";
import type { Answering, ReadRecord } from "./functions.ts";

const executable = join(import.meta.dirname, "../../lean/.lake/build/bin/tazuna-lean");

// No signal listeners: the tests talk to Lean synchronously, so a listener would not run until the synchronous work
// ends, and the process would stop exiting on signals.
const running = new Set<ChildProcess>();
process.once("exit", () => {
  for (const child of running) child.kill();
});

export type Message = Readonly<Record<string, unknown>>;

interface Ref {
  readonly service: string;
  readonly name: string;
}

export interface LeanViolation {
  readonly kind: string;
  readonly definition: Ref | null;
  readonly data: unknown;
}

export type VerifyViolation = Mismatch | Uncomparable;

const fileLines = (lines: readonly FileLine[]) =>
  lines.map((l) => (l === undefined ? null : isMalformed(l) ? "malformed" : l));

export interface LeanOutcome {
  readonly lines: readonly TraceLine[];
  readonly violations: readonly LeanViolation[];
  /** The pairs of steps whose other order test runs, by step number. */
  readonly candidates: readonly (readonly [number, number])[];
  readonly enabled: readonly Enabled[];
}

export interface LeanRun extends LeanOutcome {
  readonly handle: number;
}

interface LeanNames {
  readonly byCaller: Readonly<Record<string, boolean>>;
  readonly limits: Readonly<Record<string, number>>;
  readonly stepOrderLimit: number;
}

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

  private send(message: Message): void {
    writeSync(this.toLean, `${JSON.stringify(message)}\n`);
  }

  private receive(): Message {
    for (;;) {
      const end = this.buffered.indexOf("\n");
      if (end >= 0) {
        const line = this.parts.join("") + this.buffered.slice(0, end);
        this.parts = [];
        this.buffered = this.buffered.slice(end + 1);
        return JSON.parse(line) as Message;
      }
      this.parts.push(this.buffered);
      const n = readSync(this.fromLean, this.chunk);
      if (n === 0) throw new Error("tazuna-lean exited");
      this.buffered = this.decoder.write(this.chunk.subarray(0, n));
    }
  }

  private exchange(request: Message, answer: string, functions: Answering): Message {
    this.send(request);
    for (;;) {
      const message = this.receive();
      if (message["type"] === answer) return message;
      if (message["type"] === "error") throw new Error(`tazuna-lean: ${String(message["message"])}`);
      this.send(functions.answer(message));
    }
  }

  read(part: Parameters<ReadRecord>[0]): unknown {
    this.send({ type: "read", ...part });
    const served = this.receive();
    if (served["type"] !== "served") throw new Error(`tazuna-lean answered a read with ${JSON.stringify(served)}`);
    return served["value"];
  }

  /**
   * Runs `steps` in Lean. The returned handle names the path's state in Lean, which extend continues until the next
   * run.
   */
  run(spec: Spec, service: string, steps: readonly Step[], functions: Answering): LeanRun {
    const result = this.exchange({ type: "run", structure: spec.structure, service, steps }, "result", functions);
    return result as unknown as LeanRun;
  }

  /** Returns the run of the handle's path followed by `step`, continued from the handle's state. */
  extend(handle: number, step: Step, functions: Answering): LeanRun {
    const result = this.exchange({ type: "extend", handle, step }, "result", functions);
    return result as unknown as LeanRun;
  }

  /**
   * Returns Lean's ChoiceDependent violation, or null, for the choice of `kind` between the runs of the steps `first`
   * and `second`, in the order the relation takes them.
   */
  choice(
    spec: Spec,
    service: string,
    kind: string,
    first: readonly Step[],
    second: readonly Step[],
    functions: Answering,
  ): ChoiceDependent | null {
    const result = this.exchange(
      { type: "choice", structure: spec.structure, service, kind, first, second },
      "decided",
      functions,
    );
    return result["found"] as ChoiceDependent | null;
  }

  verify(
    spec: Spec,
    service: string,
    snapshot: readonly (TraceLine | undefined)[],
    trace: readonly FileLine[],
    functions: Answering,
  ): readonly VerifyViolation[] {
    const result = this.exchange(
      {
        type: "verify",
        structure: spec.structure,
        service,
        snapshot: snapshot.map((l) => l ?? null),
        trace: fileLines(trace),
      },
      "verified",
      functions,
    );
    return result["findings"] as VerifyViolation[];
  }

  checkExternal(spec: Spec, service: string, trace: readonly FileLine[]): readonly VerifyViolation[] {
    this.send({ type: "checkExternal", structure: spec.structure, service, trace: fileLines(trace) });
    const message = this.receive();
    if (message["type"] !== "checkedExternal")
      throw new Error(`tazuna-lean answered checkExternal with ${JSON.stringify(message)}`);
    return message["findings"] as VerifyViolation[];
  }

  afters(snapshot: readonly (TraceLine | undefined)[]): readonly VerifyViolation[] {
    this.send({ type: "afters", snapshot: snapshot.map((l) => l ?? null) });
    const message = this.receive();
    if (message["type"] !== "afters") throw new Error(`tazuna-lean answered afters with ${JSON.stringify(message)}`);
    return message["findings"] as VerifyViolation[];
  }

  decodeLines(values: readonly Json[]): readonly (Json | null)[] {
    this.send({ type: "decodeLines", values });
    const message = this.receive();
    if (message["type"] !== "decodedLines")
      throw new Error(`tazuna-lean answered decodeLines with ${JSON.stringify(message)}`);
    return message["lines"] as (Json | null)[];
  }

  pair(request: {
    readonly services: readonly { readonly name: string; readonly external: boolean }[];
    readonly scenarios: readonly PairingScenario[];
    readonly others: readonly string[];
    readonly folders: readonly Folder[];
  }): unknown {
    this.send({ type: "pair", ...request });
    const { type, ...paired } = this.receive();
    if (type !== "paired") throw new Error(`tazuna-lean answered pair with ${JSON.stringify({ type, ...paired })}`);
    return paired;
  }

  pairSnapshots(request: {
    readonly services: readonly string[];
    readonly scenarios: readonly PairingScenario[];
    readonly folders: readonly Folder[];
  }): unknown {
    this.send({ type: "pairSnapshots", ...request });
    const { type, ...paired } = this.receive();
    if (type !== "pairedSnapshots")
      throw new Error(`tazuna-lean answered pairSnapshots with ${JSON.stringify({ type, ...paired })}`);
    return paired;
  }

  compareSnapshot(snapshot: readonly (Json | undefined)[], run: readonly Json[]): VerifyViolation | null {
    this.send({ type: "compareSnapshot", snapshot: snapshot.map((l) => l ?? null), run });
    const message = this.receive();
    if (message["type"] !== "comparedSnapshot")
      throw new Error(`tazuna-lean answered compareSnapshot with ${JSON.stringify(message)}`);
    return message["mismatch"] as VerifyViolation | null;
  }

  /** Lean's verdict on the step order `order` of the processing `origin` of `service`, the last of `scenario`. */
  stepOrder(
    spec: Spec,
    scenario: Scenario,
    origin: Origin,
    service: string,
    order: readonly StepName[],
    functions: Answering,
  ): ChoiceDependent | null {
    const result = this.exchange(
      { type: "stepOrder", structure: spec.structure, scenario, origin, service, order },
      "decided",
      functions,
    );
    return result["found"] as ChoiceDependent | null;
  }

  names(): LeanNames {
    this.send({ type: "names" });
    const message = this.receive();
    if (message["type"] !== "names") throw new Error(`tazuna-lean answered names with ${JSON.stringify(message)}`);
    return {
      byCaller: message["byCaller"] as Record<string, boolean>,
      limits: message["limits"] as Record<string, number>,
      stepOrderLimit: message["stepOrderLimit"] as number,
    };
  }

  peer(request: {
    readonly service: string;
    readonly peer: string;
    readonly received: readonly string[];
    readonly fromLines: readonly number[];
    readonly state: readonly Step[];
    readonly elsewhere: readonly (readonly [number, Step])[];
    readonly lines: readonly TraceLine[];
    readonly peerLines: readonly TraceLine[];
    readonly halted: readonly [unknown, string] | null;
    readonly peerForms: readonly (readonly [string, unknown, unknown])[];
    readonly ownInputForms: readonly (readonly [string, unknown, unknown])[];
    readonly reported: readonly (readonly [unknown, unknown])[];
  }): { readonly inputs: unknown; readonly findings: unknown; readonly runFindings: unknown } {
    this.send({ type: "peer", ...request });
    const { type, ...result } = this.receive();
    if (type !== "peer") throw new Error(`tazuna-lean answered peer with ${JSON.stringify({ type, ...result })}`);
    return result as { readonly inputs: unknown; readonly findings: unknown; readonly runFindings: unknown };
  }

  /** Returns Lean's simulation of the scenario: each running service's trace and violations, and the reports. */
  /** Simulates the scenario, or with `walk` runs its lines as explore does and returns what each service enables. */
  simulate(spec: Spec, scenario: Scenario, functions: Answering, walk = false): Message {
    const { type, ...result } = this.exchange(
      { type: "simulate", structure: spec.structure, scenario, ...(walk ? { walk } : {}) },
      "simulated",
      functions,
    );
    return result;
  }

  check(structure: Structure): readonly Illegal[] {
    this.send({ type: "check", structure });
    const message = this.receive();
    if (message["type"] !== "checked") throw new Error(`tazuna-lean answered check with ${JSON.stringify(message)}`);
    return message["findings"] as Illegal[];
  }
}
