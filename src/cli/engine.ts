import { spawn, spawnSync } from "node:child_process";
import { join } from "node:path";
import { createInterface } from "node:readline";
import { InternalError } from "../data/internalError.ts";
import type { Request, Response } from "./protocol.generated.ts";

/** The Lean engine, which runs every semantics of a command: the spec's functions as the structure's IR. */
const executable = join(import.meta.dirname, "../../lean/.lake/build/bin/tazuna-engine");

/** The response that each request gets. */
const responses = {
  check: "checked",
  checkCanonical: "checkedCanonical",
  pairSnapshots: "pairedSnapshots",
  compareSnapshot: "comparedSnapshot",
  afters: "afters",
  decodeLines: "decodedLines",
  simulate: "simulated",
  test: "tested",
  verify: "verified",
  bindings: "bound",
  verifyExternal: "verifiedExternal",
  givenRecords: "given",
  readLines: "read",
  sort: "sorted",
  keyOrdered: "keyOrdered",
  evaluate: "evaluated",
  parse: "parsed",
  proveQueries: "queried",
  prove: "proved",
  generate: "generated",
} as const satisfies Record<Exclude<Request["type"], "solved">, Response["type"]>;

export type Asked = keyof typeof responses;
export type Answer<T extends Asked> = Omit<Extract<Response, { type: (typeof responses)[T] }>, "type">;

function answerOf<T extends Asked>(type: T, response: Response | null): Answer<T> {
  if (response?.type === "error") throw new InternalError(`the engine: ${response.message}`);
  if (response?.type !== responses[type])
    throw new InternalError(`the engine answered ${type} with ${JSON.stringify(response)}`);
  const { type: _, ...answer } = response;
  return answer as unknown as Answer<T>;
}

/** The engine's answers to `requests`, in order, from one run of it, which reads one JSON line per request. */
export function ask<T extends Asked>(
  type: T,
  requests: readonly Omit<Extract<Request, { type: T }>, "type">[],
): Answer<T>[] {
  const run = spawnSync(executable, {
    input: requests.map((r) => `${JSON.stringify({ type, ...r })}\n`).join(""),
    encoding: "utf8",
    maxBuffer: Number.POSITIVE_INFINITY,
  });
  if (run.error !== undefined) throw new InternalError(`cannot run ${executable}: ${run.error.message}`);
  if (run.status !== 0) throw new InternalError(`${executable} exited with ${run.status}: ${run.stderr}`);
  const lines = run.stdout.split("\n").filter((l) => l !== "");
  return requests.map((__, i) => answerOf(type, JSON.parse(lines[i] ?? "null") as Response | null));
}

/**
 * The engine's answer to `request`, from a run of it that asks `solve` for Z3's outputs on its scripts while it computes
 * the answer, each time it sends a `solve` line.
 */
export async function converse<T extends Asked>(
  type: T,
  request: Omit<Extract<Request, { type: T }>, "type">,
  solve: (scripts: readonly string[]) => Promise<string[]>,
): Promise<Answer<T>> {
  const engine = spawn(executable, { stdio: ["pipe", "pipe", "pipe"] });
  const failed = new Promise<never>((_, reject) => {
    engine.on("error", (e) => reject(new InternalError(`cannot run ${executable}: ${e.message}`)));
  });
  let stderr = "";
  engine.stderr.setEncoding("utf8").on("data", (chunk: string) => {
    stderr += chunk;
  });
  const send = (message: object) => engine.stdin.write(`${JSON.stringify(message)}\n`);
  send({ type, ...request });
  const lines = createInterface({ input: engine.stdout, crlfDelay: Number.POSITIVE_INFINITY })[Symbol.asyncIterator]();
  try {
    for (;;) {
      const next = await Promise.race([lines.next(), failed]);
      if (next.done === true) throw new InternalError(`${executable} ended without an answer: ${stderr}`);
      const response = JSON.parse(next.value) as Response;
      if (response.type !== "solve") return answerOf(type, response);
      send({ type: "solved", outputs: await solve(response.scripts) } satisfies Request);
    }
  } finally {
    engine.stdin.end();
    engine.kill();
  }
}
