import type { DefinitionRef } from "../data/definitionRef.ts";
import type { StepName } from "../data/step.generated.ts";
import type { LineId } from "../data/trace.generated.ts";
import { lineIdText } from "../data/trace.ts";
import type { Json } from "../data/values.ts";
import type { Processing } from "../service/chart/queue.ts";
import { answerIn, call, endSubscription, receive, send, subscribe } from "../service/input.ts";
import type { LineBody } from "../service/message.ts";
import { sameStep } from "../service/note.ts";
import { newStep, report } from "../service/state.ts";

/** Lean's receivedId: the id by which the receiver of a message from `sender` names the sender's id `id` of it. */
export const receivedId = (sender: string, id: LineId): LineId =>
  id.kind === "own" ? { kind: "received", sender, id: id.id } : id;

/** Lean's sentId?: the sender's id of a message that `service` received with the id `id`, when `service` sent it. */
const sentId = (service: string, id: LineId): LineId | undefined =>
  id.kind === "received" && id.sender === service ? { kind: "own", id: id.id } : undefined;

/** Lean's arriveFrom. */
export function arriveFrom(r: Processing, sender: string, id: LineId, body: LineBody): void {
  const given = { id: receivedId(sender, id) };
  switch (body.type) {
    case "command":
      send(r, body.target, body.input, given);
      return;
    case "query":
      call(r, body.target, body.input, given);
      return;
    case "subscribe":
      subscribe(r, body.target, body.input, given);
      return;
    case "unsubscribe":
      endSubscription(r, receivedId(sender, body.to));
      return;
    case "answer": {
      const own = sentId(r.st.service, body.to);
      if (own !== undefined) answerIn(r, receivedId(sender, id), own, body.answer);
      return;
    }
    case "event":
      receive(
        r,
        body.event,
        body.payload,
        given.id,
        body.resultOf === undefined ? undefined : sentId(r.st.service, body.resultOf),
      );
      return;
    default:
      return;
  }
}

/** Lean's arrivalContent: the message as `service` reads it, without the id that only names it. */
function arrivalContent(service: string, sender: string, body: LineBody): Json {
  switch (body.type) {
    case "command":
    case "query":
    case "subscribe":
      return { [body.type]: body.input as Json };
    case "event": {
      const resultOf = body.resultOf === undefined ? undefined : sentId(service, body.resultOf);
      return { event: body.payload as Json, resultOf: resultOf === undefined ? null : lineIdText(resultOf) };
    }
    case "answer":
      return { answer: body.answer as Json, to: lineIdText(sentId(service, body.to) ?? body.to) };
    case "unsubscribe":
      return { unsubscribe: lineIdText(receivedId(sender, body.to)) };
    default:
      return null;
  }
}

/** Lean's Arrival: a message of a tie. A tie has at most one message per channel, so its messages arrive in any order. */
export interface Arrival {
  readonly sender: string;
  readonly id: LineId;
  readonly body: LineBody;
  readonly definition: DefinitionRef;
}

/** Lean's Arrival.name. */
const arrivalName = (service: string, a: Arrival): StepName => ({
  kind: "arrival",
  definition: a.definition,
  content: arrivalContent(service, a.sender, a.body),
});

/** Lean's arriveAll: the messages of a tie arrive, each as its own message, in the order that the step order names. */
export function arriveAll(r: Processing, arrivals: readonly Arrival[]): void {
  const s = r.state;
  const first = s.steps.length;
  const remaining = [...arrivals];
  for (let next = remaining[0]; next !== undefined; next = remaining[0]) {
    const [named, ...rest] = s.stepOrder;
    let chosen = next;
    if (named?.kind === "arrival") {
      const found = remaining.find((a) => sameStep(arrivalName(r.st.service, a), named));
      if (found === undefined)
        report(s, {
          kind: "InvalidInput.unreadyStep",
          definition: null,
          data: { named, candidates: remaining.map((a) => arrivalName(r.st.service, a)) },
        });
      chosen = found;
      s.stepOrder = rest;
    }
    remaining.splice(remaining.indexOf(chosen), 1);
    const step = newStep(s, { kind: "arrival", tie: { kind: "arrivals", first } }, { message: s.messageCount + 1 });
    r.note.arrivalBegins(step, arrivalName(r.st.service, chosen));
    arriveFrom(r, chosen.sender, chosen.id, chosen.body);
    r.note.arrivalEnds();
  }
}
