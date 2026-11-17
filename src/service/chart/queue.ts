import type { StepName } from "../../data/choiceDependent.generated.ts";
import type { Answer } from "../../data/trace.generated.ts";
import { canonicalJson, type Fields } from "../../data/values.ts";
import type { Automation, Service } from "../basic.ts";
import type { Emit } from "../message.ts";
import { type Instance, type Requester, type Run, report, type State } from "../state.ts";
import type { Activity } from "./basic.ts";

/**
 * A command sent to its own service. `order` is the sender definition's rank, `cause` is the sending step, `serial` is
 * the serial of the Queued that awaits the answer of a command that a machine sent, and `input` is the encoded input.
 */
export interface Sent {
  readonly order: number;
  readonly requester: Exclude<Requester, { readonly kind: "slot" }>;
  readonly activity: Activity;
  readonly serial: number | undefined;
  readonly input: unknown;
  readonly cause: number;
}

/** Work for the internal queue. `cause` is the step that caused the work. */
export type Work =
  | { readonly kind: "reaction"; readonly automation: Automation; readonly event: Emit; readonly cause: number }
  | { readonly kind: "answered"; readonly sent: Sent; readonly answer: Answer; readonly cause: number }
  /** A machine or screen starts in its initial state. A screen that `opens` opened has the opening step as cause. */
  | { readonly kind: "start"; readonly machine: string; readonly cause: number | undefined }
  /** `received` holds each receives key and payload, and is empty when only records changed. */
  | {
      readonly kind: "receive";
      readonly machine: string;
      readonly received: readonly { readonly key: string; readonly payload: unknown }[];
      readonly cause: number;
    }
  | { readonly kind: "onDone"; readonly machine: string; readonly cause: number }
  /** A screen that `opens` opened closed in a final state, so the opener takes the opens onDone. */
  | {
      readonly kind: "opensDone";
      readonly machine: string;
      readonly state: string;
      readonly key: string;
      readonly output: Fields;
      readonly serial: number;
      readonly cause: number;
    };

/**
 * The internal queue of a message. `entered` holds the states with calls, sends, shows, or opens that the message
 * entered, with the entering step.
 */
export interface Queue {
  readonly tasks: Work[];
  readonly round: Sent[];
  readonly commands: Sent[];
  readonly entered: { readonly machine: string; readonly state: string; readonly step: number }[];
}

export function newQueue(): Queue {
  return { tasks: [], round: [], commands: [], entered: [] };
}

export function enter(q: Queue, machine: string, state: string, step: number): void {
  const at = q.entered.findIndex((e) => e.machine === machine && e.state === state);
  if (at >= 0) q.entered.splice(at, 1);
  q.entered.push({ machine, state, step });
}

/** Returns `sent` sorted by sender definition; commands of equal rank keep their sending order. */
function sortSent(sent: readonly Sent[]): Sent[] {
  return sent.toSorted((a, b) => a.order - b.order);
}

/** Work or an own-service command that the internal queue can take next. */
export type Ready = { readonly kind: "work"; readonly work: Work } | { readonly kind: "command"; readonly sent: Sent };

/**
 * Lean's Queue.take: removes the entry that the queue takes next and returns it, or undefined when nothing is ready.
 * While the state has `stepOrder` entries, the taken entry is the first ready one that the next entry names (`name`
 * names each). Otherwise, it is the first in queue order: the tasks in arrival order, then the commands, with the round
 * joined to them in sender-definition order. An entry that names a deadline waits for its tie (chooseDeadline), so the
 * queue takes the first in queue order and keeps the entry.
 */
export function take(r: Processing, name: (ready: Ready) => StepName): Ready | undefined {
  const { state: s, queue } = r;
  const [named, ...rest] = s.stepOrder;
  const first = (): Ready | undefined => {
    const work = queue.tasks.shift();
    if (work !== undefined) return { kind: "work", work };
    queue.commands.push(...sortSent(queue.round.splice(0)));
    const sent = queue.commands.shift();
    return sent === undefined ? undefined : { kind: "command", sent };
  };
  if (named === undefined) return first();
  const commands = [...queue.commands, ...sortSent(queue.round)];
  const ready = [
    ...queue.tasks.map((work): Ready => ({ kind: "work", work })),
    ...commands.map((sent): Ready => ({ kind: "command", sent })),
  ];
  if (ready.length === 0) return undefined;
  const i = ready.findIndex((entry) => canonicalJson(name(entry)) === canonicalJson(named));
  if (i < 0 && named.kind === "deadline") return first();
  if (i < 0)
    return report(s, {
      kind: "InvalidInput.unreadyStep",
      definition: null,
      data: { named, candidates: ready.map(name) },
    });
  s.stepOrder = rest;
  if (i < queue.tasks.length) queue.tasks.splice(i, 1);
  else {
    commands.splice(i - queue.tasks.length, 1);
    queue.commands.splice(0, queue.commands.length, ...commands);
    queue.round.splice(0);
  }
  return ready[i];
}

/** Lean's Processing: the State and the internal queue of the current message, and what Lean passes beside them. */
export interface Processing extends Run {
  readonly queue: Queue;
}

/**
 * Returns the receive work of `instance`. Always guards may read records, so a record change re-evaluates always
 * transitions even without an event.
 */
function machineWork(
  emits: readonly Emit[],
  recordsChanged: boolean,
  cause: number,
  instance: Instance,
): Work | undefined {
  const received = emits.flatMap((e) =>
    instance.chart.receives.filter(([, event]) => event === e.event).map(([key]) => ({ key, payload: e.payload })),
  );
  if (instance.closed || (received.length === 0 && !recordsChanged)) return undefined;
  return { kind: "receive", machine: instance.resource, received, cause };
}

/** Returns the work that `emits` cause. Copies get no work; they move with their owner's evaluation. */
export function reactions(
  st: Service,
  s: State,
  emits: readonly Emit[],
  recordsChanged: boolean,
  cause: number,
): Work[] {
  return [
    ...[...s.machines.values()].flatMap((i) => machineWork(emits, recordsChanged, cause, i) ?? []),
    ...emits.flatMap((e) =>
      st.automations
        .filter((a) => a.receives === e.event)
        .map((automation): Work => ({ kind: "reaction", automation, event: e, cause })),
    ),
  ];
}

/** Returns the work that a command's events cause. Writing an event counts as a record change. */
export function commandWork(st: Service, s: State, emits: readonly Emit[], cause: number): Work[] {
  return emits.length === 0 ? [] : reactions(st, s, emits, true, cause);
}
