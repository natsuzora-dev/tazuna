import type { Answer, Rejection } from "./trace.generated.ts";

/**
 * What a command's caller receives. Only an external service's command that declares `output` has `output` when
 * accepted.
 */
export type CommandAnswer<O = undefined> =
  | ([O] extends [undefined] ? { readonly result: "accepted" } : { readonly result: "accepted"; readonly output: O })
  | { readonly result: "rejected"; readonly rejection: Rejection };

/** What a query's caller receives. */
export type QueryAnswer<O = unknown> =
  | { readonly result: "fulfilled"; readonly output: O }
  | { readonly result: "rejected"; readonly rejection: Rejection };

/** Lean's Answer.unavailable. */
export const unavailable = (answer: Answer): boolean =>
  "rejection" in answer && answer.rejection.kind === "unavailable";

/** Lean's Answer.mapOutput. */
export const mapOutput = (answer: Answer, f: (v: unknown) => unknown): Answer =>
  "output" in answer ? ({ ...answer, output: f(answer.output) } as Answer) : answer;
