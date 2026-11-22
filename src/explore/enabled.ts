import type { LineId } from "../data/trace.generated.ts";
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
     * The payloads encoded as in the trace, or null when no offers apply and every payload that matches the schema is
     * accepted.
     */
    readonly payloads: readonly unknown[] | null;
  }[];
  readonly awaiting: readonly {
    readonly id: LineId;
    readonly name: string;
    readonly target: string;
    readonly sender: string;
  }[];
  /** The time of the next deadline, absent when there is none. */
  readonly nextDeadline?: number;
}

function nextDeadline(s: State): number | undefined {
  return s.deadlines.reduce<number | undefined>(
    (best, t) => (best === undefined || t.time < best ? t.time : best),
    undefined,
  );
}

export function enabled(r: Processing): Enabled {
  return r.evaluations.quietly(() => {
    const next = nextDeadline(r.state);
    return {
      operations: [...new Set(r.state.stack)]
        .flatMap((id) => operationsOf(r, id))
        .map(({ screen, id, control, payloads }) => ({ screen, id, control, payloads: payloads ?? null })),
      awaiting: r.state.pending.map((p) => ({
        id: p.id,
        name: p.activity.target.name,
        target: p.activity.target.service,
        sender: sender(p.requester),
      })),
      ...(next === undefined ? {} : { nextDeadline: next }),
    };
  });
}
