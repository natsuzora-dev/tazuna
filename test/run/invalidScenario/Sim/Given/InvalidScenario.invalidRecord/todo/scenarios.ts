import { parseInstant } from "@natsuzora-dev/tazuna";
import { addTask, scenario } from "./todo.ts";

export const untitled = scenario({
  description: "Given writes a task with an empty title, which the schema of Task rejects",
  given: {
    start: parseInstant("2026-10-25T09:00:00+09:00"),
    records: { Task: [{ id: "task-1", title: "" }] },
    peers: [],
  },
  when: (w) => {
    w.client.send(addTask, { taskId: "task-2", title: "Buy milk" });
  },
  then: () => [],
});
