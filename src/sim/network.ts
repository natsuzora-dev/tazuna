import type { StepName } from "../data/choiceDependent.generated.ts";
import type { DefinitionRef } from "../data/definitionRef.ts";
import { haltingInvalidScenarioKinds, type InvalidScenario } from "../data/invalidScenario.generated.ts";
import type { Fact, Origin } from "../data/scenario.generated.ts";
import type { TraceLine } from "../data/trace.generated.ts";
import { contentOf } from "../data/trace.ts";
import { byCodePoint, stringsOf } from "../data/values.ts";
import type { Violation } from "../data/violation.ts";
import { ref } from "../service/basic.ts";
import type { Processing } from "../service/chart/queue.ts";
import type { Records } from "../service/records.ts";
import { created, Halt, report, type State } from "../service/state.ts";
import { isKeyOf, refOfTraceName } from "../spec/structure.ts";
import { arriveFrom, nameIn, receivedId, senderOf } from "./participant.ts";

/** Lean's Role. */
export type Role = "own" | "run" | "external" | "skip";

export const running = (role: Role | undefined): boolean => role === "own" || role === "run";

/** Lean's Status. */
export type Status = "inFlight" | "delivered" | "lost" | "unanswered" | "discarded";

/** Lean's Message: `body` is the line that `sender` wrote. */
export interface Message {
  readonly sender: string;
  readonly receiver: string;
  readonly id: string;
  readonly body: TraceLine;
  readonly origin: Origin;
  readonly channel: string | undefined;
  status: Status;
}

/** Lean's Message.describe. */
export const describe = (m: Message) => ({ sender: m.sender, receiver: m.receiver, id: m.id, origin: m.origin });

export const sameChannel = (m: Message, n: Message): boolean =>
  m.sender === n.sender && m.receiver === n.receiver && m.channel === n.channel;

export const sameOrigin = (a: Origin, b: Origin): boolean =>
  a.type === b.type && (a.type === "startup" || (b.type === "line" && a.index === b.index));

export interface Span {
  readonly origin: Origin;
  readonly service: string;
  readonly from: number;
  readonly to: number;
  readonly stepsFrom: number;
  readonly stepsTo: number;
}

/** Lean's World.stepOrders entry. */
export interface StepOrder {
  readonly origin: Origin;
  readonly service: string;
  readonly order: readonly StepName[];
}

/** Lean's World.assignments entry: a group of handles of `requests`, and the place of the message of each handle. */
export type Assignment = readonly [Fact, readonly number[]];

export interface Opened {
  readonly origin: Origin;
  readonly service: string;
  readonly chart: string;
  readonly resource: string;
}

export interface Sent {
  readonly line: number;
  readonly receiver: string;
  readonly id: string;
  readonly position: number;
}

export interface Participant {
  readonly processing: Processing;
  halted: Violation | undefined;
}

/** Lean's World. The running services are in `participants`, the own service first. */
export interface World {
  now: Temporal.Instant;
  readonly roles: ReadonlyMap<string, Role>;
  readonly participants: ReadonlyMap<string, Participant>;
  readonly messages: Message[];
  readonly spans: Span[];
  readonly opened: Opened[];
  readonly sent: Sent[];
  readonly carried: (readonly [number, number])[];
  /** The messages that leaveInFlight lines name: the line, and the message. */
  readonly leftInFlight: (readonly [number, number])[];
  /** Lean's World.counts. */
  readonly counts: Map<string, number>;
  readonly violations: InvalidScenario[];
  halted: InvalidScenario | undefined;
  /** Lean's World.stepOrders. */
  stepOrders: readonly StepOrder[];
  /** Lean's World.assignments. */
  assignments: readonly Assignment[];
}

export const stateOf = (w: World, service: string): State | undefined => w.participants.get(service)?.processing.state;

/** Lean's World.stopped. */
export const stopped = (w: World): boolean =>
  w.halted !== undefined || [...w.participants.values()].some((p) => p.halted !== undefined);

const halting: ReadonlySet<string> = new Set(haltingInvalidScenarioKinds);

/** Lean's World.report. */
export function reportTo(w: World, r: InvalidScenario): void {
  if (halting.has(r.kind)) w.halted = r;
  else w.violations.push(r);
}

/** Lean's World.note: a report of Given or of an expectation of Then, which stops nothing. */
export function noteTo(w: World, r: InvalidScenario): void {
  w.violations.push(r);
}

/** Lean's screensOf. */
const screensOf = (s: State): string[] =>
  [...s.machines.values()].filter((i) => i.chart.screen).map((i) => `${i.chart.name}\u0000${i.resource}`);

/** Lean's targetOf. */
function targetOf(service: string, lines: readonly TraceLine[], id: string): string | undefined {
  for (const l of lines)
    if (l.dir === "out" && (l.type === "command" || l.type === "query" || l.type === "subscribe") && l.id === id)
      return refOfTraceName(service, l.name).service;
  return undefined;
}

/** Lean's World.post. */
function post(w: World, o: Origin, sender: string, receiver: string, l: TraceLine, channel: string | undefined): void {
  const role = w.roles.get(receiver);
  if (role === undefined) {
    reportTo(w, {
      kind: "InvalidScenario.unlistedService",
      definition: null,
      data: { scenarioLine: o.type === "line" ? o.index : null, service: receiver },
    });
    return;
  }
  w.messages.push({
    sender,
    receiver,
    id: l.id,
    body: l,
    origin: o,
    channel,
    status: role === "skip" ? "discarded" : "inFlight",
  });
}

/** Lean's World.route. */
function route(w: World, o: Origin, service: string, lines: readonly TraceLine[]): void {
  for (const l of lines) {
    if (l.dir !== "out" || stopped(w)) continue;
    const own = receivedId(service, l.id);
    switch (l.type) {
      case "command":
      case "query":
      case "subscribe": {
        const target = refOfTraceName(service, l.name).service;
        if (target !== service) post(w, o, service, target, l, own);
        break;
      }
      case "unsubscribe": {
        const target = targetOf(service, stateOf(w, service)?.lines ?? [], l.to);
        if (target !== undefined) post(w, o, service, target, l, receivedId(service, l.to));
        break;
      }
      case "answer": {
        const requester = senderOf(l.to);
        if (requester !== undefined) post(w, o, service, requester, l, l.to);
        break;
      }
      case "event":
        for (const [r, p] of w.participants)
          if (r !== service && p.processing.st.receives.includes(nameIn(service, r, l.name)))
            post(w, o, service, r, l, l.resultOf);
        break;
      default:
        break;
    }
  }
}

/** Lean's World.keyEntity?: the keyed entity of a running participant whose key form the string `x` has. */
export function keyEntity(w: World, x: string): DefinitionRef | undefined {
  for (const [owner, { processing }] of w.participants) {
    const { st } = processing;
    const entity = st.entities.find((e) => !st.singles.includes(e) && isKeyOf(`${owner}/${e}`, x));
    if (entity !== undefined) return ref(st, entity);
  }
  return undefined;
}

/** Lean's World.computedKey?. */
function computedKey(
  w: World,
  sent: readonly TraceLine[],
  records: Records,
): readonly [string, DefinitionRef] | undefined {
  const strings = [
    ...sent.filter((l) => l.dir === "out").flatMap((l) => stringsOf(contentOf(l))),
    ...[...records.keyed.values()].flatMap((rows) =>
      [...rows].flatMap(([key, row]) => [key, ...stringsOf(row.encoded)]),
    ),
    ...[...records.singles.values()].flatMap((row) => stringsOf(row.encoded)),
  ];
  const made = new Set([...w.participants.values()].flatMap((p) => created(p.processing.state).map(([, key]) => key)));
  const [least] = strings.filter((x) => !made.has(x) && keyEntity(w, x) !== undefined).toSorted(byCodePoint);
  const entity = least === undefined ? undefined : keyEntity(w, least);
  return least === undefined || entity === undefined ? undefined : [least, entity];
}

/** Lean's World.checkComputed. */
function checkComputed(w: World, service: string, sent: readonly TraceLine[], records: Records): void {
  if (w.halted !== undefined) return;
  const found = computedKey(w, sent, records);
  if (found !== undefined)
    reportTo(w, {
      kind: "InvalidScenario.computedKey",
      definition: null,
      data: { service, key: found[0], entity: found[1] },
    });
}

/** Lean's World.act. */
export function act(w: World, o: Origin, service: string, f: (r: Processing) => void, reopen = false): void {
  const p = w.participants.get(service);
  if (p === undefined) return;
  const r = p.processing;
  const s = r.state;
  const before = s.lines.length;
  const stepsFrom = s.steps.length;
  const screens = screensOf(s);
  const entry = w.stepOrders.find((e) => sameOrigin(e.origin, o) && e.service === service);
  s.stepOrder = entry?.order ?? [];
  if (entry !== undefined) w.stepOrders = w.stepOrders.filter((e) => e !== entry);
  try {
    f(r);
    const left = s.stepOrder;
    s.stepOrder = [];
    if (entry !== undefined && left.length > 0)
      report(s, { kind: "InvalidInput.unusedStepOrder", definition: null, data: { entries: left } });
  } catch (error) {
    if (!(error instanceof Halt)) throw error;
    s.stepOrder = [];
    p.halted = error.violation;
  }
  for (const key of screensOf(s).filter((k) => reopen || !screens.includes(k))) {
    const [chart = "", resource = ""] = key.split("\u0000");
    w.opened.push({ origin: o, service, chart, resource });
  }
  w.spans.push({ origin: o, service, from: before, to: s.lines.length, stepsFrom, stepsTo: s.steps.length });
  const sent = s.lines.slice(before);
  route(w, o, service, sent);
  checkComputed(w, service, sent, s.records);
}

/** Lean's World.deliver. */
export function deliver(w: World, o: Origin, k: number): void {
  const m = w.messages[k];
  if (m === undefined) return;
  m.status = "delivered";
  act(w, o, m.receiver, (r) => arriveFrom(r, m.sender, m.id, m.body));
}
