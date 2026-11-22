import { parseInstant } from "@natsuzora-dev/tazuna";
import { logTitle, scenario } from "./todo.ts";

export const logFarDate = scenario({
  description:
    "Log a title from 2026-10-25; decide moves the date three million days on, past year 9999, so addDays throws and test reports exception of logTitle",
  given: { start: parseInstant("2026-10-25T09:00:00+09:00"), records: {}, peers: [] },
  when: (w) => {
    w.client.send(logTitle, { title: "Buy milk", from: "2026-10-25" });
  },
  then: () => [],
});
