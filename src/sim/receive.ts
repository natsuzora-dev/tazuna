import { receivedId, sentId } from "../data/trace.ts";
import type { Processing } from "../service/chart/queue.ts";
import { answerIn, call, endSubscription, receive, send, subscribe } from "../service/input.ts";
import type { LineBody } from "../service/message.ts";

/** Lean's arriveFrom. */
export function arriveFrom(r: Processing, sender: string, id: string, body: LineBody): void {
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
        given,
        body.resultOf === undefined ? undefined : sentId(r.st.service, body.resultOf),
      );
      return;
    default:
      return;
  }
}
