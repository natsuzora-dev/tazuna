import { addTask, scenario, seenIds } from "./todo.ts";

export const seenOnce = scenario(
  "Add a task and ask twice for the seen ids; the key that taskAdded's internal seen event creates binds where the first seenIds answer holds it; no violation",
  {
    given: { start: "2026-10-25T00:00:00Z", records: { Task: [], Seen: [] }, peers: {} },
    when: (w) => {
      w.client.send(addTask, { taskId: "task-1" });
      w.client.call(seenIds, {});
      w.client.call(seenIds, {});
    },
    then: () => [],
  },
);

export const seenOnceWrongListed = scenario(
  "Same inputs as seenOnce; the implementation trace of this scenario answers the second seenIds with another key in listed, which does not stand for the bound key, so verify reports Mismatch.output",
  {
    given: { start: "2026-10-25T00:00:00Z", records: { Task: [], Seen: [] }, peers: {} },
    when: (w) => {
      w.client.send(addTask, { taskId: "task-1" });
      w.client.call(seenIds, {});
      w.client.call(seenIds, {});
    },
    then: () => [],
  },
);
