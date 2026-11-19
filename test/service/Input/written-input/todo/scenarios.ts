import { emission, emitted, raw } from "@natsuzora-dev/tazuna";
import { addItem, itemAdded, scenario } from "./todo.ts";

const given = { start: "2026-10-25T09:00:00+09:00", records: {}, peers: {} } as const;

export const writtenAsIs = scenario(
  "Add an item whose note has spaces and capitals and whose quantity is a string; the in line holds the input as the client wrote it, and only todo's parse trims, lowercases and coerces it",
  {
    given,
    when: (w) => ({ adding: w.client.send(addItem, { note: "  MILK ", qty: raw("5") }) }),
    then: ({ adding }) => [emitted(adding, [emission(itemAdded, { note: "milk", qty: 5 })])],
  },
);
