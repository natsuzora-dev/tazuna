import type { TraceLine } from "../data/trace.generated.ts";
import type { Processing } from "../service/chart/queue.ts";
import { answerIn, call, endSubscription, receive, send, subscribe } from "../service/input.ts";
import { refOfTraceName, traceNameOfRef } from "../spec/structure.ts";

/** Lean's receivedId. */
export const receivedId = (sender: string, id: string): string => `${sender}/${id}`;

/** Lean's sentId?. */
const sentId = (service: string, id: string): string | undefined =>
  id.startsWith(`${service}/`) ? id.slice(service.length + 1) : undefined;

/** Lean's senderOf?. */
export function senderOf(id: string): string | undefined {
  const parts = id.split("/");
  return parts.length === 2 ? parts[0] : undefined;
}

/** Lean's nameIn. */
export const nameIn = (sender: string, receiver: string, name: string): string =>
  traceNameOfRef(refOfTraceName(sender, name), receiver);

/** Lean's arriveFrom. */
export function arriveFrom(r: Processing, sender: string, id: string, line: TraceLine): void {
  const name = (n: string) => nameIn(sender, r.st.service, n);
  const given = { id: receivedId(sender, id) };
  switch (line.type) {
    case "command":
      send(r, name(line.name), line.input, given);
      return;
    case "query":
      call(r, name(line.name), line.input, given);
      return;
    case "subscribe":
      subscribe(r, name(line.name), line.input, given);
      return;
    case "unsubscribe":
      endSubscription(r, receivedId(sender, line.to));
      return;
    case "answer": {
      const own = sentId(r.st.service, line.to);
      if (own !== undefined) answerIn(r, receivedId(sender, id), own, line.answer);
      return;
    }
    case "event":
      receive(
        r,
        name(line.name),
        line.payload,
        given,
        line.resultOf === undefined ? undefined : sentId(r.st.service, line.resultOf),
      );
      return;
    default:
      return;
  }
}
