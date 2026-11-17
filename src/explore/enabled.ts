import type { Processing } from "../service/chart/queue.ts";
import type { InstanceId } from "../service/instance.ts";
import { operationsOf } from "../service/screen/operable.ts";
import { type State, sender } from "../service/state.ts";

/**
 * What a run accepts next: the operations of the open screens, the requests that await answers, and the next deadline.
 * It holds JSON values only.
 */
export interface Enabled {
  readonly operations: readonly {
    readonly screen: string;
    /** The open screen instance. */
    readonly id: InstanceId;
    readonly control: string;
    /**
     * The payloads encoded as in the trace, or "any" when no offers apply and every payload that matches the schema is
     * accepted.
     */
    readonly payloads: readonly unknown[] | "any";
  }[];
  readonly awaiting: readonly {
    readonly id: string;
    readonly name: string;
    readonly target: string;
    readonly sender: string;
  }[];
  /** The time of the next deadline, absent when no deadline has a time. */
  readonly nextDeadline?: string;
}

function nextDeadline(s: State): Temporal.Instant | undefined {
  return s.deadlines.reduce<Temporal.Instant | undefined>(
    (best, t) =>
      t.time === undefined ? best : best === undefined || Temporal.Instant.compare(t.time, best) < 0 ? t.time : best,
    undefined,
  );
}

export function enabled(r: Processing): Enabled {
  return r.evaluations.quietly(() => {
    const next = nextDeadline(r.state);
    return {
      operations: [...new Set(r.state.stack)]
        .flatMap((id) => operationsOf(r, id))
        .map(({ screen, id, control, payloads }) => ({ screen, id, control, payloads: payloads ?? "any" })),
      awaiting: r.state.pending.map((p) => ({
        id: p.id,
        name: p.activity.target.name,
        target: p.activity.target.service,
        sender: sender(p.requester),
      })),
      ...(next === undefined ? {} : { nextDeadline: next.toString() }),
    };
  });
}
