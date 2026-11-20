import { expectFound } from "../../data/internalError.ts";
import type { Activity, Requester } from "../../data/step.generated.ts";
import type { Fields, Json } from "../../data/values.ts";
import { withExtra } from "../../data/violation.ts";
import { ref } from "../basic.ts";
import { Failed, firstFalse, issueViolation, parseSorted, sorted } from "../functions.ts";
import { type InstanceId, openedId, ownerId } from "../instance.ts";
import { LazyRecordSource } from "../records.ts";
import {
  awaitAnswer,
  createKeys,
  documentOrder,
  halt,
  type Instance,
  inStep,
  machine,
  NoteAccess,
  newStep,
  nextKeys,
  report,
  scopeOf,
  startQueued,
} from "../state.ts";
import { type Chart, isOwn } from "./basic.ts";
import { slots } from "./config.ts";
import type { Processing } from "./queue.ts";

/**
 * Lean's initialContextOf: what the initialContext of `chart` computes from `input`, with each field that it leaves out
 * taking its default, sorted and parsed, or a halt with what an Issue means.
 */
export function initialContextOf(r: Processing, chart: string, input: Fields): Fields {
  const definition = ref(r.st, chart);
  const fault = (failed: Failed) =>
    halt(issueViolation(definition, failed, () => ({ kind: "Fault.initialContextSchema", definition, data: {} })));
  const given = r.functions.initialContext(chart, input);
  if (given instanceof Failed) return fault(given);
  const schema = { kind: "context", chart: definition } as const;
  const defaults = r.functions.defaults(schema);
  if (defaults instanceof Failed) return fault(defaults);
  const parsed = parseSorted(r.st, r.functions, schema, merged(defaults, given));
  if (parsed instanceof Failed) return fault(parsed);
  if ("error" in parsed)
    return halt(withExtra({ kind: "Fault.initialContextSchema", definition, data: {} }, { error: parsed.error }));
  return parsed.value;
}

/** Lean's Value.merge: the fields of `a` with those of `b` over them, or `b` when either is no object. */
function merged(a: unknown, b: Json): Json {
  const isObject = (v: unknown): v is Readonly<Record<string, Json>> =>
    v !== null && typeof v === "object" && !Array.isArray(v);
  return isObject(a) && isObject(b) ? { ...a, ...b } : b;
}

export function newInstance(
  chart: Chart,
  id: InstanceId,
  { input, context }: { readonly input: Fields; readonly context: Fields },
): Instance {
  return {
    chart,
    id,
    context,
    input,
    entered: new Map(),
    lastChildren: new Map(),
    closed: false,
    awaitingOnDone: undefined,
    shown: new Map(slots(chart).map((slot) => [slot, null])),
    copyKeys: new Map(),
    held: new Map(),
  };
}

function request(r: Processing, instance: Instance, state: string, a: Activity, step: number): void {
  const definition = ref(r.st, instance.chart.name);
  const target = a.target;
  const scope = scopeOf(r.state, instance, state);
  const records = new LazyRecordSource(r.state.records, r.note);
  const given = r.functions.input(scope, records, a, nextKeys(r.state), new NoteAccess(r, scope));
  if (given instanceof Failed) halt(issueViolation(definition, given));
  createKeys(r.state, given.created);
  const input = sorted(r.st, { kind: "input", definition: target }, given.input);
  const requester: Requester = { kind: "state", machine: instance.id, state };
  if (isOwn(a, r.st.service)) {
    r.queue.round.push({
      order: instance.chart.order,
      requester,
      activity: a,
      serial: startQueued(r.state, instance.id, state),
      input,
      cause: step,
    });
    return;
  }
  const type = a.keyword === "calls" ? "query" : "command";
  awaitAnswer(r.state, { type, target: a.target, input }, requester, a);
  r.note.reached({ kind: "request", definition: target, data: {} });
}

function openScreen(r: Processing, step: number, instance: Instance, state: string, a: Activity): void {
  const child = r.st.charts.get(a.target.name);
  if (child === undefined) return;
  const definition = ref(r.st, instance.chart.name);
  const screen = ref(r.st, child.name);
  const scope = scopeOf(r.state, instance, state);
  const records = new LazyRecordSource(r.state.records, r.note);
  const given = r.functions.input(scope, records, a, nextKeys(r.state), new NoteAccess(r, scope));
  if (given instanceof Failed) halt(issueViolation(definition, given));
  const schema = { kind: "input", definition: screen } as const;
  const parsed = parseSorted(r.st, r.functions, schema, given.input);
  if (parsed instanceof Failed) halt(issueViolation(screen, parsed));
  if ("error" in parsed)
    halt(withExtra({ kind: "Fault.inputSchema", definition, data: { target: screen } }, { error: parsed.error }));
  const input = parsed.value;
  const condition = firstFalse(
    (c) => r.functions.inputRequirement(screen, c, input),
    expectFound(`requirements of ${child.name}`, r.st.requirements.get(child.name)).requires,
  );
  if (condition instanceof Failed) halt(issueViolation(screen, condition));
  if (condition !== undefined)
    report(r.state, { kind: "Fault.failedRequires", definition, data: { screen, condition } });
  const context = initialContextOf(r, child.name, input);
  const s = r.state;
  const created = newInstance(child, openedId(child.name, instance.id, state, a.key), { input, context });
  s.machines.delete(created.id);
  s.machines.set(created.id, created);
  s.stack.push(created.id);
  r.queue.tasks.push({ kind: "start", machine: created.id, cause: step });
}

/** Sends the requests and opens the screens of state `name`; a `shows` subscribes after evaluation. */
function activate(r: Processing, instance: Instance, name: string, step: number): void {
  for (const a of instance.chart.states.get(name)?.activities ?? []) {
    if (a.keyword === "opens") openScreen(r, step, instance, name, a);
    else if (a.keyword !== "shows") request(r, instance, name, a, step);
  }
}

/** SCXML statesToInvoke. */
export function sendEntered(r: Processing): void {
  const entered = r.queue.entered.splice(0);
  for (const owner of new Set(entered.map((e) => ownerId(e.machine)))) {
    const instance = machine(r.state, owner);
    if (instance === undefined) continue;
    for (const { holder, n } of documentOrder(r.state, instance)) {
      const e = entered.find((e) => e.machine === holder.id && e.state === n);
      if (e === undefined || holder.closed || !holder.entered.has(n)) continue;
      const step = newStep(r.state, { kind: "caused", cause: e.step }, { barrier: true });
      inStep(r, step, { kind: "activities", id: holder.id, state: n }, undefined, () => activate(r, holder, n, step));
    }
  }
}
