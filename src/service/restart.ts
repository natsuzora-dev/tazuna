import { Subscriptions } from "../data/subscriptions.ts";
import type { Processing } from "./chart/queue.ts";
import { begin } from "./input.ts";
import { type State, write } from "./state.ts";

/**
 * Stops the service process, discarding the part of the state that lives in its memory: the instances, copies, open
 * screens, deadlines, awaited requests, queued work, and the subscriptions that other services opened. As in the Raft
 * TLA+ spec's Restart, the persisted part stays: the records, the kept command answers and event deliveries, the
 * accepted external commands, the createKey values, and the trace.
 */
function stop(s: State): void {
  s.started = false;
  s.machines.clear();
  s.copies.clear();
  s.stack.length = 0;
  s.deadlines.length = 0;
  s.pending.length = 0;
  s.queued.length = 0;
  s.subscriptions = new Subscriptions();
}

/**
 * Processes a restart input. The process stops after the deadlines due by then fire, and the service begins again as at
 * the first input. Answers to the requests of the stopped process find no waiting request.
 */
export function restart(r: Processing): void {
  write(r.state, { dir: "in", type: "restart" });
  stop(r.state);
  begin(r);
}
