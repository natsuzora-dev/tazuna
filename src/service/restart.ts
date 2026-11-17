import type { Processing } from "./chart/queue.ts";
import { begin } from "./input.ts";
import { newProcess, write } from "./state.ts";

/**
 * Processes a restart input. The process stops after the deadlines due by then fire, dropping the part of the state that
 * lives in its memory, and the service begins again as at the first input. Answers to the requests of the stopped
 * process find no waiting request.
 */
export function restart(r: Processing): void {
  write(r.state, { dir: "in", type: "restart" });
  Object.assign(r.state, newProcess());
  begin(r);
}
