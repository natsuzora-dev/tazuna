import { arm, scenario, title } from "./tasks.ts";

export const subscribed = scenario({
  description:
    "Subscribe to title and arm at 11:00; the deadlines of first and second tie. They add different tasks, and no answer after either deadline's message reads the tasks, so test runs no other order and reports nothing",
  given: { start: "2026-10-25T11:00:00+09:00", records: { Task: [], Board: { title: "" } }, peers: [] },
  when: (w) => {
    w.client.subscribe(title, {});
    w.client.send(arm, {});
  },
  then: () => [],
});
