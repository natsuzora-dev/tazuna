import { scenario, taskCount } from "./todo.ts";

export const countAtEachTime = scenario(
  "Count at a time with ten fraction digits, at a time with a part below a millisecond, and at a time with zeros below a millisecond; the first two are unparsable",
  {
    given: { start: "2026-10-25T09:00:00+09:00", records: {}, peers: {} },
    when: (w) => {
      w.clock.at("2026-10-25T09:02:00.1234567891+09:00");
      w.client.call(taskCount, {});
      w.clock.at("2026-10-25T09:03:00.0009+09:00");
      w.client.call(taskCount, {});
      w.clock.at("2026-10-25T09:04:00.001000+09:00");
      w.client.call(taskCount, {});
    },
    then: () => [],
  },
);
