import { parseInstant } from "@natsuzora-dev/tazuna";
import { addTask, scenario } from "./todo.ts";

export const addOne = scenario({
  description:
    "Add a task; traces/todo/addOne.jsonl replays without a violation, while the folder traces/other names no service of the spec, so verify reports unknownService",
  given: { start: parseInstant("2026-10-25T00:00:00Z"), records: { Task: [] }, peers: [] },
  when: (w) => {
    w.client.send(addTask, { taskId: "task-1", title: "Buy milk" });
  },
  then: () => [],
});
