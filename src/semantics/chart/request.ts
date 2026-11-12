import type { Fields } from "../../data/values.ts";
import { Failed, issueViolation } from "../functions.ts";
import { ref, requirementsOf, type Service } from "../service/basic.ts";
import { firstFalse } from "../service/contract.ts";
import { LazyRecordSource } from "../service/records.ts";
import {
  awaitAnswer,
  awaitedActivities,
  createKeys,
  documentOrder,
  halt,
  type Instance,
  inStep,
  instanceWho,
  keyCounts,
  machine,
  NoteAccess,
  newStep,
  ownerOf,
  type Requester,
  report,
  scopeOf,
  senderOf,
  startQueued,
  who,
} from "../state.ts";
import { type Activity, activityRef, type Chart } from "./basic.ts";
import { slots } from "./config.ts";
import type { Processing } from "./queue.ts";

/** Returns the initial context of `chart` started with `input`, or halts with what an Issue of initialContext means. */
export function initialContextOf(r: Processing, chart: string, input: Fields): Fields {
  const definition = ref(r.st, chart);
  const context = r.functions.initialContext(chart, input);
  if (context instanceof Failed)
    return halt(
      issueViolation(definition, context, () => ({ kind: "Fault.initialContextSchema", definition, data: {} })),
    );
  return context;
}

export function newInstance(
  st: Service,
  chart: Chart,
  resource: string,
  { input, context }: { readonly input: Fields; readonly context: Fields },
  opener: Instance["opener"],
): Instance {
  const fields = {
    chart,
    resource,
    context,
    input,
    entered: new Map(),
    lastChildren: new Map(),
    closed: false,
    awaitingOnDone: undefined,
    shown: new Map(slots(chart).map((slot) => [slot, null])),
    ...(opener === undefined ? {} : { opener }),
    copyKeys: new Map(),
  };
  return { ...fields, who: instanceWho(fields, st) };
}

function request(r: Processing, instance: Instance, state: string, a: Activity, step: number): void {
  const definition = ref(r.st, instance.chart.name);
  const target = activityRef(a);
  const scope = scopeOf(r.state, instance, state);
  const records = new LazyRecordSource(r.state.records, r.note);
  const checked = r.functions.input(scope, records, a, keyCounts(r.state), new NoteAccess(r, scope));
  if (checked instanceof Failed)
    halt(
      issueViolation(definition, checked, () => ({ kind: "Fault.requestInputSchema", definition, data: { target } })),
    );
  createKeys(r.state, checked.created);
  const { value, encoded } = checked;
  const requester: Requester = { kind: "state", machine: instance.resource, state };
  if (a.own) {
    r.queue.round.push({
      order: instance.chart.order,
      requester,
      activity: a,
      serial: startQueued(r.state, instance.resource, state),
      input: encoded,
      cause: step,
    });
    return;
  }
  r.note.requested(a, senderOf(r.state, requester), awaitedActivities(r.state));
  const type = a.keyword === "calls" ? "query" : "command";
  awaitAnswer(r.state, { dir: "out", type, name: a.target, input: encoded }, requester, a, value);
  r.note.reached({ kind: "request", definition: target, data: {} });
}

function openScreen(r: Processing, step: number, instance: Instance, state: string, a: Activity): void {
  const child = r.st.charts.get(a.name);
  if (child === undefined) return;
  const definition = ref(r.st, instance.chart.name);
  const screen = ref(r.st, child.name);
  const scope = scopeOf(r.state, instance, state);
  const records = new LazyRecordSource(r.state.records, r.note);
  const given = r.functions.input(scope, records, a, keyCounts(r.state), new NoteAccess(r, scope));
  if (given instanceof Failed)
    halt(issueViolation(definition, given, () => ({ kind: "Fault.screenInputSchema", definition, data: { screen } })));
  const input = given.value;
  const condition = firstFalse(
    (c) => r.functions.inputRequirement(child.name, c, input),
    requirementsOf(r.st, child.name).requires,
  );
  if (condition instanceof Failed) halt(issueViolation(screen, condition));
  if (condition !== undefined)
    report(r.state, { kind: "Fault.failedRequires", definition, data: { screen, condition } });
  const context = initialContextOf(r, child.name, input);
  const s = r.state;
  const opener = { parent: instance.resource, state, key: a.key, modal: a.modal };
  const opened = [...s.machines.values()].filter((i) => i.chart.name === child.name).length;
  const resource = opened === 0 ? child.name : `${child.name}(${opened + 1})`;
  const created = newInstance(r.st, child, resource, { input, context }, opener);
  s.machines.set(created.resource, created);
  s.stack.push(created.resource);
  r.queue.tasks.push({ kind: "start", machine: created.resource, cause: step });
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
  for (const owner of new Set(entered.map((e) => ownerOf(r.state, e.machine)))) {
    const instance = machine(r.state, owner);
    if (instance === undefined) continue;
    for (const { holder, n } of documentOrder(r.state, instance)) {
      const e = entered.find((e) => e.machine === holder.resource && e.state === n);
      if (e === undefined || holder.closed || !holder.entered.has(n)) continue;
      const step = newStep(r.state, e.step, { barrier: true });
      inStep(r, step, { kind: "activities", who: who(r.state, r.st, holder.resource), state: n }, undefined, () =>
        activate(r, holder, n, step),
      );
    }
  }
}
