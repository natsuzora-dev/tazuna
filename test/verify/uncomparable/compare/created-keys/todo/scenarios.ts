import { addTask, forget, scenario, seenOf } from "./todo.ts";

export const forgetFirst = scenario(
  "Add two tasks, ask for the seen key of the first, and forget it; the implementation trace of this scenario creates the seen keys in the other order and gives the snapshot's key verbatim, which is the implementation's key of the second task, so verify reports differentInput",
  {
    given: { start: "2026-10-25T00:00:00Z", records: { Task: [], Seen: [] }, peers: {} },
    when: (w) => {
      w.client.send(addTask, { taskId: "task-1" });
      w.client.send(addTask, { taskId: "task-2" });
      const first = w.client.call(seenOf, { taskId: "task-1" });
      w.client.send(forget, { id: first.output.id });
    },
    then: () => [],
  },
);

export const forgetOne = scenario(
  "Add a task, ask for its seen key, and forget it; the implementation trace of this scenario gives forget the snapshot's key verbatim instead of the key z1 that the implementation created and answered, so verify reports differentInput",
  {
    given: { start: "2026-10-25T00:00:00Z", records: { Task: [], Seen: [] }, peers: {} },
    when: (w) => {
      w.client.send(addTask, { taskId: "task-1" });
      const seen = w.client.call(seenOf, { taskId: "task-1" });
      w.client.send(forget, { id: seen.output.id });
    },
    then: () => [],
  },
);
