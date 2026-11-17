import type { Processing } from "../service/chart/queue.ts";
import { operationsOf } from "../service/screen/operable.ts";
import { machine, type State, senderOf } from "../service/state.ts";

/**
 * What a run accepts next: the operations of the open screens, the requests that await answers, and the next deadline.
 * It holds JSON values only.
 */
export interface Enabled {
  readonly operations: readonly {
    readonly screen: string;
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
      operations: openScreens(r.state)
        .flatMap((screen) => operationsOf(r, screen))
        .map(({ screen, control, payloads }) => ({ screen, control, payloads: payloads ?? "any" })),
      awaiting: r.state.pending.map((p) => ({
        id: p.id,
        name: p.activity.target.name,
        target: p.activity.target.service,
        sender: senderOf(r.state, p.requester),
      })),
      ...(next === undefined ? {} : { nextDeadline: next.toString() }),
    };
  });
}

function openScreens(s: State): string[] {
  return [...new Set(s.stack.flatMap((resource) => machine(s, resource)?.chart.name ?? []))];
}
