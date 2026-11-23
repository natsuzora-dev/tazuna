import { type ChildProcess, execFileSync, spawn } from "node:child_process";
import { closeSync, mkdtempSync, openSync, readSync, rmSync, writeSync } from "node:fs";
import { tmpdir } from "node:os";
import { join } from "node:path";
import { StringDecoder } from "node:string_decoder";
import { fileURLToPath } from "node:url";
import type { Evaluated, Keys, Request, Response, Stored } from "../../src/cli/protocol.generated.ts";
import type { Json } from "../../src/data/values.ts";
import type { Expr } from "../../src/spec/ir.generated.ts";

const executable = fileURLToPath(import.meta.resolve("#engine"));

// No signal listeners: the tests talk to Lean synchronously, so a listener would not run until the synchronous work
// ends, and the process would stop exiting on signals.
const running = new Set<ChildProcess>();
process.once("exit", () => {
  for (const child of running) child.kill();
});

/** The response that each request that these tests send gets. */
const responses = {
  decodeLines: "decodedLines",
  evaluate: "evaluated",
  parse: "parsed",
} as const satisfies Partial<Record<Request["type"], Response["type"]>>;

type Responded<T extends keyof typeof responses> = Omit<Extract<Response, { type: (typeof responses)[T] }>, "type">;

/**
 * The engine process, which a test asks many small questions inside one synchronous property check: stdin and stdout
 * go through two named pipes, and readSync waits for each answer.
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
    this.dir = mkdtempSync(join(tmpdir(), "tazuna-engine-"));
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
  private send(message: Request): void {
    writeSync(this.toLean, `${JSON.stringify(message)}\n`);
  }
  private receive(): Response {
    for (;;) {
      const end = this.buffered.indexOf("\n");
      if (end >= 0) {
        const line = this.parts.join("") + this.buffered.slice(0, end);
        this.parts = [];
        this.buffered = this.buffered.slice(end + 1);
        return JSON.parse(line) as Response;
      }
      this.parts.push(this.buffered);
      const n = readSync(this.fromLean, this.chunk);
      if (n === 0) throw new Error("tazuna-engine exited");
      this.buffered = this.decoder.write(this.chunk.subarray(0, n));
    }
  }

  /** Sends `request` and returns the engine's response. */
  private exchange<T extends keyof typeof responses>(
    type: T,
    request: Omit<Extract<Request, { type: T }>, "type">,
  ): Responded<T> {
    this.send({ type, ...request } as unknown as Request);
    const message = this.receive();
    if (message.type === "error") throw new Error(`tazuna-engine: ${message.message}`);
    if (message.type !== responses[type]) throw new Error(`tazuna-engine answered ${type} with ${message.type}`);
    const { type: _, ...response } = message;
    return response as unknown as Responded<T>;
  }

  decodeLines(values: readonly Json[]): Responded<"decodeLines">["lines"] {
    return this.exchange("decodeLines", { values }).lines;
  }
  /**
   * The value of `body` with `input` as its only argument over `records` and createKey over `keys`, as Lean evaluates
   * the IR, its reads, and the entities it made keys of. `fields` names each entity's fields, which a record writes.
   */
  evaluate(
    body: Expr,
    input: Json,
    records: readonly Stored[],
    keys: Keys,
    fields: Readonly<Record<string, readonly string[]>>,
  ): Evaluated {
    return this.exchange("evaluate", { body, input, records, keys, fields }).result;
  }
  /** `value` parsed by the JSON Schema `schema` as Lean parses, or undefined where Lean leaves the schema to Zod. */
  parse(schema: Json, value: Json): Omit<Responded<"parse">, "supported"> | undefined {
    const { supported, ...parsed } = this.exchange("parse", { schema, value });
    return supported ? parsed : undefined;
  }
}
