import { parseInstant } from "@natsuzora-dev/tazuna";
import { addTask, scenario } from "./todo.ts";

export const addTwice = scenario({
  description:
    "Add two tasks with one line each at 10:00; todo sends every output of the first addTask, including the logged event of the log command that logAdded sends, before it processes the second addTask, so the work of the two commands never interleaves although they arrive at one time",
  given: { start: parseInstant("2026-10-25T10:00:00+09:00"), records: {}, peers: [] },
  when: (w) => {
    w.client.send(addTask, { taskId: "task-1" });
    w.client.send(addTask, { taskId: "task-2" });
  },
  then: () => [],
});
