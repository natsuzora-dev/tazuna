import { parseInstant } from "@natsuzora-dev/tazuna";
import { addTask, scenario } from "./todo.ts";

export const addTwoCut = scenario({
  description:
    "Add two tasks; the trace has a line that the trace line schema cannot read after the second request, so verify reports that line and compares no line after the second request",
  given: { start: parseInstant("2026-10-25T00:00:00Z"), records: { Task: [] }, peers: [] },
  when: (w) => {
    w.client.as("client").send(addTask, { taskId: "task-1", title: "Buy milk" });
    w.client.as("client").send(addTask, { taskId: "task-2", title: "Buy eggs" });
  },
  then: () => [],
});
