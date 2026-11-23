import { parseInstant } from "@natsuzora-dev/tazuna";
import { addTask, scenario, taskTitle } from "./todo.ts";

export const copyRejected = scenario({
  description:
    "Ask for the title of the task with an empty taskId, which todo rejects, and add a task with the title in the output of that answer, which has no output",
  given: { start: parseInstant("2026-10-25T09:00:00+09:00"), records: { Task: [] }, peers: [] },
  when: (w) => {
    const asking = w.client.as("client").call(taskTitle, { taskId: "" });
    w.client.as("client").send(addTask, { taskId: "task-1", title: asking.output.title });
  },
  then: () => [],
});
