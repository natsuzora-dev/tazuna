import { sameRef } from "../../data/definitionRef.ts";
import type { Activity, Received, Requester, StepName } from "../../data/step.generated.ts";
import type { Answer } from "../../data/trace.generated.ts";
import type { Fields } from "../../data/values.ts";
import type { Automation, Service } from "../basic.ts";
import type { InstanceId } from "../instance.ts";
import type { Emitted } from "../message.ts";
import { sameStep } from "../note.ts";
import { type Instance, type Run, report, type State } from "../state.ts";

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

/** Lean's Received, with the payload also decoded, which only TS has. */
export type ReceivedEvent = Received & { readonly decoded: unknown };

/** Work for the internal queue. `cause` is the step that caused the work. */
export type Work =
  /** `groups` holds the events that the automation receives, in their groups, like a receive work's. */
  | {
      readonly kind: "reaction";
      readonly automation: Automation;
      readonly groups: readonly (readonly Emitted[])[];
      readonly delivered: readonly (readonly Emitted[])[];
      readonly cause: number;
    }
  | { readonly kind: "answered"; readonly sent: Sent; readonly answer: Answer; readonly cause: number }
  /** A machine or screen starts in its initial state. A screen that `opens` opened has the opening step as cause. */
  | { readonly kind: "start"; readonly machine: InstanceId; readonly cause: number | undefined }
  /**
   * `groups` holds each receives key and payload in the groups of the events, and is empty when only records changed.
   * One step takes one event; the next group waits for the current one. `delivered` holds the groups as the work
   * received them.
   */
  | {
      readonly kind: "receive";
      readonly machine: InstanceId;
      readonly groups: readonly (readonly ReceivedEvent[])[];
      readonly delivered: readonly (readonly ReceivedEvent[])[];
      readonly cause: number;
    }
  | { readonly kind: "onDone"; readonly machine: InstanceId; readonly cause: number }
  /** A screen that `opens` opened closed in a final state, so the opener takes the opens onDone. */
  | {
      readonly kind: "opensDone";
      readonly machine: InstanceId;
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
  readonly entered: { readonly machine: InstanceId; readonly state: string; readonly step: number }[];
}

export function newQueue(): Queue {
  return { tasks: [], round: [], commands: [], entered: [] };
}

export function enter(q: Queue, machine: InstanceId, state: string, step: number): void {
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

/** A ready entry and the position of its task, or of its command after the tasks. */
export interface Entry {
  readonly ready: Ready;
  readonly at: number;
}

/** Lean's Groups.choices: any item of the first group may come first, since a group has no order. The first is `groups`. */
function groupChoices<T>(groups: readonly (readonly T[])[]): (readonly (readonly T[])[])[] {
  const [group, ...later] = groups;
  const [e, ...others] = group ?? [];
  if (e === undefined) return [groups];
  return [groups, ...others.map((x, k) => [[x, e, ...others.toSpliced(k, 1)], ...later])];
}

/**
 * Lean's Groups.rest: the groups left after a step took the first item, and their cause. The rest of the group keeps
 * `cause`; the next group waits for the one before it, so `step` causes it.
 */
function groupsLeft<T>(
  groups: readonly (readonly T[])[],
  cause: number,
  step: number,
): { readonly groups: readonly (readonly T[])[]; readonly cause: number } | undefined {
  const [group, ...later] = groups;
  if (group === undefined || group.length === 0) return undefined;
  if (group.length > 1) return { groups: [group.slice(1), ...later], cause };
  return later.length === 0 ? undefined : { groups: later, cause: step };
}

/** Lean's Work.choices: a receive or reaction work takes any event of its first group first. The first is `work`. */
function choices(work: Work): Work[] {
  if (work.kind === "receive") return groupChoices(work.groups).map((groups) => ({ ...work, groups }));
  if (work.kind === "reaction") return groupChoices(work.groups).map((groups) => ({ ...work, groups }));
  return [work];
}

/** Lean's Work.rest: what is left of a receive or reaction work after `step` took its first event. */
export function workLeft(work: Work, step: number): Work | undefined {
  if (work.kind === "receive") {
    const left = groupsLeft(work.groups, work.cause, step);
    return left && { ...work, ...left };
  }
  if (work.kind === "reaction") {
    const left = groupsLeft(work.groups, work.cause, step);
    return left && { ...work, ...left };
  }
  return undefined;
}

/** Lean's Queue.entries. */
function entries(queue: Queue): Entry[] {
  return [
    ...queue.tasks.flatMap((task, at) => choices(task).map((work): Entry => ({ ready: { kind: "work", work }, at }))),
    ...[...queue.commands, ...sortSent(queue.round)].map(
      (sent, j): Entry => ({ ready: { kind: "command", sent }, at: queue.tasks.length + j }),
    ),
  ];
}

/** Lean's Queue.without: removes the task or command at `at`. Taking a command joins the round to the commands. */
function without(queue: Queue, at: number): void {
  if (at < queue.tasks.length) {
    queue.tasks.splice(at, 1);
    return;
  }
  const commands = [...queue.commands, ...sortSent(queue.round)];
  commands.splice(at - queue.tasks.length, 1);
  queue.commands.splice(0, queue.commands.length, ...commands);
  queue.round.splice(0);
}

/**
 * Lean's Queue.take: removes the entry that the queue takes next and returns it, or undefined when nothing is ready.
 * While the state has `stepOrder` entries, the taken entry is the first ready one that the next entry names (`name`
 * names each). Otherwise, it is the first in queue order: the tasks in arrival order, then the commands, with the round
 * joined to them in sender-definition order. An entry that names a deadline waits for its tie (chooseDeadline), and one
 * that names an arrival for the next message of a tie (arriveAll), so the queue takes the first in queue order and keeps
 * the entry.
 */
export function take(r: Processing, name: (ready: Ready) => StepName): Entry | undefined {
  const { state: s, queue } = r;
  const [named, ...rest] = s.stepOrder;
  const ready = entries(queue);
  const [first] = ready;
  if (first === undefined) return undefined;
  if (named === undefined) {
    without(queue, first.at);
    return first;
  }
  const found = ready.find((e) => sameStep(name(e.ready), named));
  if (found === undefined && named.kind !== "deadline" && named.kind !== "arrival")
    return report(s, {
      kind: "InvalidInput.unreadyStep",
      definition: null,
      data: { named, candidates: ready.map((e) => name(e.ready)) },
    });
  if (found !== undefined) s.stepOrder = rest;
  const taken = found ?? first;
  without(queue, taken.at);
  return taken;
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
  groups: readonly (readonly Emitted[])[],
  recordsChanged: boolean,
  cause: number,
  instance: Instance,
): Work | undefined {
  const received = groups
    .map((g) =>
      g.flatMap((e) =>
        instance.chart.receives
          .filter(([, event]) => sameRef(event, e.event))
          .map(([key]): ReceivedEvent => ({ key, payload: e.encoded, decoded: e.payload })),
      ),
    )
    .filter((g) => g.length > 0);
  if (instance.closed || (received.length === 0 && !recordsChanged)) return undefined;
  return { kind: "receive", machine: instance.id, groups: received, delivered: received, cause };
}

/**
 * Returns the work that the groups of events cause: one receive work per machine and one reaction work per automation,
 * each with its events in their groups. Copies get no work; they move with their owner's evaluation.
 */
export function reactions(
  st: Service,
  s: State,
  groups: readonly (readonly Emitted[])[],
  recordsChanged: boolean,
  cause: number,
): Work[] {
  return [
    ...[...s.machines.values()].flatMap((i) => machineWork(groups, recordsChanged, cause, i) ?? []),
    ...st.automations.flatMap((automation): Work[] => {
      const received = groups
        .map((g) => g.filter((e) => sameRef(e.event, automation.receives)))
        .filter((g) => g.length > 0);
      return received.length === 0
        ? []
        : [{ kind: "reaction", automation, groups: received, delivered: received, cause }];
    }),
  ];
}

/** Returns the work that a command's groups of events cause. Writing an event counts as a record change. */
export function commandWork(st: Service, s: State, groups: readonly (readonly Emitted[])[], cause: number): Work[] {
  return groups.every((g) => g.length === 0) ? [] : reactions(st, s, groups, true, cause);
}
