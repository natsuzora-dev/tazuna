import { parseInstant } from "@natsuzora-dev/tazuna";
import { scenario, taskCount } from "./todo.ts";

const start = parseInstant("2026-10-25T09:00:00+09:00");

export const countAtEachTime = scenario({
  description:
    "Count at a time with a fraction of a millisecond, at a time past every safe integer, and at a whole millisecond; all but the third are inexact",
  given: { start, records: {}, peers: [] },
  when: (w) => {
    w.clock.at(start + 0.5);
    w.client.call(taskCount, {});
    w.clock.at(2 ** 53);
    w.client.call(taskCount, {});
    w.clock.at(start + 60_000);
    w.client.call(taskCount, {});
  },
  then: () => [],
});
