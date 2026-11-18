import type { LineId } from "../data/trace.generated.ts";
import type { Processing } from "../service/chart/queue.ts";
import { answerIn, call, endSubscription, receive, send, subscribe } from "../service/input.ts";
import type { LineBody } from "../service/message.ts";

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
