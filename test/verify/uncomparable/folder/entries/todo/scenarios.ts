import { parseInstant } from "@natsuzora-dev/tazuna";
import { addTask, scenario } from "./todo.ts";

export const addOne = scenario({
  description:
    'Add a task. Every file under traces/todo is a trace of todo, whatever its name or depth: addOne.jsonl, addOne/explored.jsonl and "any name.log" replay without a violation, addOne.txt has a line that the trace line schema cannot read, and traces/addOne.jsonl is in no service\'s folder, so verify reports lineSchema and unknownTraceEntry',
  given: { start: parseInstant("2026-10-25T00:00:00Z"), records: { Task: [] }, peers: [] },
  when: (w) => {
    w.client.send(addTask, { taskId: "task-1", title: "Buy milk" });
  },
  then: () => [],
});
