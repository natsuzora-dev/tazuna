import { addTask, scenario } from "./todo.ts";

export const syncedWithinMessage = scenario(
  "Add two tasks; after the transition on taskAdded, added and shown differ and tally breaks its invariant inSync, but an always transition in the same message brings shown in line. tally checks its invariants when the message is processed, so no violation is reported",
  {
    given: { start: "2026-10-25T10:00:00+09:00", records: {}, peers: [] },
    when: (w) => {
      w.client.send(addTask, { taskId: "task-1" });
      w.client.send(addTask, { taskId: "task-2" });
    },
    then: () => [],
  },
);
