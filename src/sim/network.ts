import { haltingReportKinds, type Report } from "../data/report.generated.ts";
import type { Origin } from "../data/scenario.generated.ts";
import type { TraceLine } from "../data/trace.generated.ts";
import type { Violation } from "../data/violation.ts";
import type { Processing } from "../service/chart/queue.ts";
import { Halt, type State } from "../service/state.ts";
import { refOfTraceName } from "../syntax/structure.ts";
import { arriveFrom, receivedId, renamed, senderOf } from "./participant.ts";

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

export const describe = (m: Message) => ({ sender: m.sender, receiver: m.receiver, id: m.id });

export const sameChannel = (m: Message, n: Message): boolean =>
  m.sender === n.sender && m.receiver === n.receiver && m.channel === n.channel;

export const sameOrigin = (a: Origin, b: Origin): boolean =>
  a.type === b.type && (a.type === "begin" || (b.type === "line" && a.index === b.index));

interface Span {
  readonly origin: Origin;
  readonly service: string;
  readonly from: number;
  readonly to: number;
}

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
}

/** A running service: its processing, and the violation that halted it. */
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
  readonly inFlight: (readonly [string, string, string | undefined])[];
  readonly emitted: Map<string, number>;
  readonly looked: (readonly [number, boolean])[];
  readonly reports: Report[];
  halted: Report | undefined;
}

export const stateOf = (w: World, service: string): State | undefined => w.participants.get(service)?.processing.state;

/** Lean's World.stopped. */
export const stopped = (w: World): boolean =>
  w.halted !== undefined || [...w.participants.values()].some((p) => p.halted !== undefined);

const halting: ReadonlySet<string> = new Set(haltingReportKinds);

/** Lean's World.report. */
export function reportTo(w: World, r: Report): void {
  if (halting.has(r.kind)) w.halted = r;
  else w.reports.push(r);
}

/** Lean's World.keysFor. */
function keysFor(w: World, service: string): [string, number][] {
  const others = [...w.participants]
    .filter(([q]) => q !== service)
    .flatMap(([, p]) => p.processing.state.created.map(([e]) => e));
  return [...new Set(others)].map((e) => [e, others.filter((o) => o === e).length]);
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
      kind: "Report.unlistedService",
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
          if (r !== service && p.processing.st.received.includes(renamed(service, r, l.name)))
            post(w, o, service, r, l, l.resultOf);
        break;
      default:
        break;
    }
  }
}

/** Lean's World.act. */
export function act(w: World, o: Origin, service: string, f: (r: Processing) => void): void {
  const p = w.participants.get(service);
  if (p === undefined) return;
  const r = p.processing;
  const s = r.state;
  s.keysBefore = keysFor(w, service);
  const before = s.lines.length;
  const screens = screensOf(s);
  try {
    f(r);
  } catch (error) {
    if (!(error instanceof Halt)) throw error;
    p.halted = error.violation;
  }
  for (const key of screensOf(s).filter((k) => !screens.includes(k))) {
    const [chart = "", resource = ""] = key.split("\u0000");
    w.opened.push({ origin: o, service, chart, resource });
  }
  w.spans.push({ origin: o, service, from: before, to: s.lines.length });
  route(w, o, service, s.lines.slice(before));
}

/** Lean's World.deliver. */
export function deliver(w: World, o: Origin, k: number): void {
  const m = w.messages[k];
  if (m === undefined) return;
  m.status = "delivered";
  act(w, o, m.receiver, (r) => arriveFrom(r, m.sender, m.id, m.body));
}
