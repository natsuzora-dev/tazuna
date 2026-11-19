import { run } from "@natsuzora-dev/tazuna";
import { ledger } from "../ledger/contract.ts";
import { priceItem, scenario } from "./todo.ts";

const given = { start: "2026-10-25T09:00:00+09:00", records: {}, peers: [run(ledger, {})] } as const;

export const encodedNested = scenario(
  "Price an item; priceRecorded sends record with the amount inside a record and a tuple, each encoded by its codec as todo writes it, so ledger's parse takes it",
  {
    given,
    when: (w) => {
      const priced = w.client.send(priceItem, { item: "milk", cents: 250 });
      const recorded = w.net.deliver(priced.request(ledger.record));
      w.net.deliver(recorded.answer(recorded));
    },
    then: () => [],
  },
);
