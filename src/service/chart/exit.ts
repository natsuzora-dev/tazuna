import { limits } from "../../data/limits.generated.ts";
import type { Requester } from "../../data/step.generated.ts";
import type { Fields } from "../../data/values.ts";
import { exitOrder, recordedChildren } from "../../spec/tree.ts";
import { ref } from "../basic.ts";
import { type Assignment, Failed, issueViolation } from "../functions.ts";
import { copyId, type InstanceId, ownerId } from "../instance.ts";
import { LazyRecordSource } from "../records.ts";
import {
  copyKeysOf,
  createKeys,
  halt,
  type Instance,
  machine,
  NoteAccess,
  nextKeys,
  type Pending,
  removeFromStack,
  report,
  type State,
  scopeOf,
  write,
} from "../state.ts";
import type { Processing } from "./queue.ts";

/** Lean's State.endSubscription. */
export function stateEndSubscription(r: Processing, p: Pending): void {
  p.stale = true;
  write(r.state, { dir: "out", type: "unsubscribe", to: p.id, request: p.activity.target });
}

type ShowsRequest = Pending & { readonly requester: Extract<Requester, { readonly kind: "slot" }> };

export function openShows(s: State, owner: InstanceId): ShowsRequest[] {
  return s.pending.filter(
    (p): p is ShowsRequest => p.requester.kind === "slot" && p.requester.machine === owner && !p.stale,
  );
}

export function recordHistory(instance: Instance, name: string): void {
  const recorded = recordedChildren(instance.chart.tree, instance.entered, name);
  if (recorded !== null) instance.lastChildren.set(name, recorded);
}

export function runAssign(
  r: Processing,
  instance: Instance,
  assignment: Assignment,
  extra: Fields,
  state: string | null,
): void {
  const definition = ref(r.st, instance.chart.name);
  const scope = scopeOf(r.state, instance, state);
  const records = new LazyRecordSource(r.state.records, r.note);
  const assigned = r.functions.assign(scope, records, assignment, extra, nextKeys(r.state), new NoteAccess(r, scope));
  if (assigned instanceof Failed)
    halt(
      issueViolation(definition, assigned, (schema) =>
        schema.kind === "mapContext"
          ? { kind: "Fault.copyContextSchema", definition, data: { map: schema.map } }
          : { kind: "Fault.contextSchema", definition, data: {} },
      ),
    );
  createKeys(r.state, assigned.created);
  if (instance.id.kind !== "copy") {
    instance.context = assigned.context;
    return;
  }
  const owner = machine(r.state, ownerId(instance.id));
  if (owner !== undefined) owner.context = assigned.context;
  instance.context = assigned.copyContext ?? instance.context;
}

/**
 * Exits every active state in exitOrder and then stops, like SCXML exitInterpreter. A closed instance stays in State,
 * so an assign of a transition that a copy closed in the same microstep chose reads the copy's values at exit.
 */
export function endWith(r: Processing, name: InstanceId, fuel: number): void {
  const instance = machine(r.state, name);
  if (instance === undefined) return;
  for (const n of exitOrder(instance.chart.tree, instance.entered)) exitOne(r, fuel, instance, n);
  instance.closed = true;
  for (const p of openShows(r.state, name)) stateEndSubscription(r, p);
  removeFromStack(r.state, name);
}

function leaveState(s: State, instance: Instance, n: string): void {
  const name = instance.id;
  instance.entered.delete(n);
  for (let i = s.deadlines.length - 1; i >= 0; i -= 1) {
    const t = s.deadlines[i];
    if (t && t.machine === name && t.state === n) s.deadlines.splice(i, 1);
  }
  for (const p of s.pending)
    if (p.requester.kind === "state" && p.requester.machine === name && p.requester.state === n) p.stale = true;
  for (const q of s.queued) if (q.machine === name && q.state === n) q.stale = true;
}

function childrenOf(s: State, name: InstanceId, n: string): InstanceId[] {
  return [...s.machines.values()]
    .filter((child) => !child.closed && child.opener?.parent === name && child.opener.state === n)
    .map((child) => child.id);
}

function leaveWith(r: Processing, fuel: number, instance: Instance, n: string): void {
  runAssign(r, instance, { kind: "exit", state: n }, {}, n);
  r.note.wroteState(instance.id, n);
  leaveState(r.state, instance, n);
  for (const child of childrenOf(r.state, instance.id, n)) endWith(r, child, fuel);
}

/** Exits state `n` of `instance`, after its copies; `fuel` is the remaining nesting depth of exits. */
export function exitOne(r: Processing, fuel: number, instance: Instance, n: string): void {
  if (fuel === 0)
    report(r.state, { kind: "Fault.exceededExitDepth", definition: null, data: { limit: limits.exitDepth } });
  for (const k of copyKeysOf(instance, n).toReversed()) endWith(r, copyId(instance.id, n, k), fuel - 1);
  instance.copyKeys.delete(n);
  leaveWith(r, fuel - 1, instance, n);
}
