import { type ChildProcess, execFileSync, spawn } from "node:child_process";
import { closeSync, mkdtempSync, openSync, readSync, rmSync, writeSync } from "node:fs";
import { tmpdir } from "node:os";
import { join } from "node:path";
import { StringDecoder } from "node:string_decoder";
import type { Illegal } from "../../src/data/illegal.generated.ts";
import type { Mismatch } from "../../src/data/mismatch.generated.ts";
import type { Scenario } from "../../src/data/scenario.generated.ts";
import type { TraceLine } from "../../src/data/trace.generated.ts";
import { type FileLine, isMalformed } from "../../src/data/trace.ts";
import type { Uncomparable } from "../../src/data/uncomparable.generated.ts";
import type { Json } from "../../src/data/values.ts";
import type { AssignmentSearch } from "../../src/explore/assignments.ts";
import type { Searched } from "../../src/explore/stepOrders.ts";
import type { Spec } from "../../src/load/load.ts";
import type { StepOrder } from "../../src/sim/network.ts";
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

interface LeanNames {
  readonly byCaller: Readonly<Record<string, boolean>>;
  readonly limits: Readonly<Record<string, number>>;
  readonly stepOrderLimit: number;
  readonly assignmentLimit: number;
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

  verify(
    spec: Spec,
    service: string,
    snapshot: readonly (TraceLine | undefined)[],
    trace: readonly FileLine[],
    functions: Answering,
  ): {
    readonly findings: readonly VerifyViolation[];
    readonly bindings: readonly (readonly (readonly [string, string])[])[];
  } {
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
    return {
      findings: result["findings"] as VerifyViolation[],
      bindings: result["bindings"] as [string, string][][],
    };
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

  /** Lean's stepOrderChanges of the scenario walked from its begin: each search, what it ran, and what it found. */
  stepOrderChanges(spec: Spec, scenario: Scenario, functions: Answering): readonly Searched[] {
    const result = this.exchange(
      { type: "stepOrderChanges", structure: spec.structure, scenario },
      "stepOrderChanges",
      functions,
    );
    return result["searched"] as readonly Searched[];
  }

  /** Lean's assignmentSearch of the scenario's handle groups: each assignment it ran, and what it found. */
  assignmentChanges(spec: Spec, scenario: Scenario, functions: Answering): AssignmentSearch {
    const { tried, found } = this.exchange(
      { type: "assignmentChanges", structure: spec.structure, scenario },
      "assignmentChanges",
      functions,
    );
    return { tried, found } as AssignmentSearch;
  }

  names(): LeanNames {
    this.send({ type: "names" });
    const message = this.receive();
    if (message["type"] !== "names") throw new Error(`tazuna-lean answered names with ${JSON.stringify(message)}`);
    return {
      byCaller: message["byCaller"] as Record<string, boolean>,
      limits: message["limits"] as Record<string, number>,
      stepOrderLimit: message["stepOrderLimit"] as number,
      assignmentLimit: message["assignmentLimit"] as number,
    };
  }

  /** Simulates the scenario, or with `walk` runs its lines as explore does and returns what each service enables. */
  simulate(
    spec: Spec,
    scenario: Scenario,
    functions: Answering,
    walk = false,
    stepOrders: readonly StepOrder[] = [],
  ): Message {
    const { type, ...result } = this.exchange(
      {
        type: "simulate",
        structure: spec.structure,
        scenario,
        ...(walk ? { walk } : {}),
        ...(stepOrders.length > 0 ? { stepOrders } : {}),
      },
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
