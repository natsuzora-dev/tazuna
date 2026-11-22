import { spawnSync } from "node:child_process";
import { join } from "node:path";
import { InternalError } from "../data/internalError.ts";
import type { Request, Response } from "./protocol.generated.ts";

/** The Lean engine, which runs every semantics of a command: the spec's functions as the structure's IR. */
const executable = join(import.meta.dirname, "../../lean/.lake/build/bin/tazuna-engine");

/** The response that each request gets. */
const responses = {
  check: "checked",
  checkCanonical: "checkedCanonical",
  pair: "paired",
  pairSnapshots: "pairedSnapshots",
  compareSnapshot: "comparedSnapshot",
  afters: "afters",
  decodeLines: "decodedLines",
  simulate: "simulated",
  test: "tested",
  verifyTrace: "verifiedTrace",
  verifyExternal: "verifiedExternal",
  givenRecords: "given",
  readLines: "read",
  sort: "sorted",
  keyOrdered: "keyOrdered",
  evaluate: "evaluated",
  parse: "parsed",
} as const satisfies Record<Request["type"], Response["type"]>;

export type Asked = keyof typeof responses;
export type Answer<T extends Asked> = Omit<Extract<Response, { type: (typeof responses)[T] }>, "type">;

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
  return requests.map((__, i) => {
    const response = JSON.parse(lines[i] ?? "null") as Response | null;
    if (response?.type === "error") throw new InternalError(`the engine: ${response.message}`);
    if (response?.type !== responses[type])
      throw new InternalError(`the engine answered ${type} with ${JSON.stringify(response)}`);
    const { type: _, ...answer } = response;
    return answer as unknown as Answer<T>;
  });
}
