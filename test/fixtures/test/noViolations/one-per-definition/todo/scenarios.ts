import { parseInstant } from "@natsuzora-dev/tazuna";
import { addTask, scenario } from "./todo.ts";

export const oneGreeter = scenario({
  description:
    "Add two tasks; only one greeter starts, at 10:00 when todo starts, and greets for the first time, and the same greeter counts up and greets on each addTask",
  given: { start: parseInstant("2026-10-25T10:00:00+09:00"), records: {}, peers: [] },
  when: (w) => {
    w.client.as("client").send(addTask, { taskId: "task-1" });
    w.client.as("client").send(addTask, { taskId: "task-2" });
  },
  then: () => [],
});
