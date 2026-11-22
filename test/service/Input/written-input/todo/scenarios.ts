import { emitted, eventOf, parseInstant } from "@natsuzora-dev/tazuna";
import { addItem, given, itemAdded, scenario } from "./todo.ts";

const arranged = given({ start: parseInstant("2026-10-25T09:00:00+09:00"), records: {}, peers: [] });

export const writtenAsIs = scenario({
  description:
    "Add an item without a quantity; the in line holds the input as the client wrote it, and only todo's parse fills the default quantity",
  given: arranged,
  when: (w) => ({ adding: w.client.send(addItem, { note: "milk" }) }),
  then: ({ adding }) => [emitted(adding, [eventOf(itemAdded, { note: "milk", qty: 1 })])],
});
