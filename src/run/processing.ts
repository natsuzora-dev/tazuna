import type { Location } from "../data/violation.ts";
import { newQueue, type Processing } from "../semantics/chart/queue.ts";
import type { Functions } from "../semantics/functions.ts";
import type { Note } from "../semantics/note.ts";
import type { Service } from "../semantics/service/basic.ts";
import { type Evaluations, newState } from "../semantics/state.ts";

/**
 * Returns a new processing of the service `st`. `listener` hears the notes and keeps the evaluation cache, and the run
 * asks `functions` about the service.
 */
export function newProcessing(
  st: Service,
  functions: Functions,
  listener: Note & Evaluations,
  place: Location | undefined,
): Processing {
  return { state: newState(st), queue: newQueue(), st, functions, note: listener, evaluations: listener, place };
}
