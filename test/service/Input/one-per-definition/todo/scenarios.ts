import { addTask, scenario } from "./todo.ts";

export const oneGreeter = scenario(
  "Add two tasks; only one greeter starts, at 10:00 when todo starts, and greets for the first time, and the same greeter counts up and greets on each addTask",
  {
    given: { start: "2026-10-25T10:00:00+09:00", records: {}, peers: {} },
    when: (w) => {
      w.client.send(addTask, { taskId: "task-1" });
      w.client.send(addTask, { taskId: "task-2" });
    },
    then: () => [],
  },
);
