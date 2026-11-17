import { addTask, scenario, seenTwice } from "./todo.ts";

export const seenSeven = scenario(
  "Add seven tasks and ask for the seen ids with task-1's repeated; the count binds Seen-1, but the six other keys of the bag bind to the implementation's in 720 ways that no line tells apart, more than verify keeps, so verify reports Uncomparable.bindingLimit",
  {
    given: { start: "2026-10-25T00:00:00Z", records: { Task: [], Seen: [] }, peers: {} },
    when: (w) => {
      for (const n of [1, 2, 3, 4, 5, 6, 7]) w.client.send(addTask, { taskId: `task-${n}` });
      w.client.call(seenTwice, {});
    },
    then: () => [],
  },
);
