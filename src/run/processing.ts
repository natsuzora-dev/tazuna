import type { Location } from "../data/violation.ts";
import type { Service } from "../service/basic.ts";
import { newQueue, type Processing } from "../service/chart/queue.ts";
import type { Functions } from "../service/functions.ts";
import type { Note } from "../service/note.ts";
import { type Evaluations, newState } from "../service/state.ts";

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
