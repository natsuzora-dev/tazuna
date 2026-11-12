import type { Rejection } from "./trace.generated.ts";

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
