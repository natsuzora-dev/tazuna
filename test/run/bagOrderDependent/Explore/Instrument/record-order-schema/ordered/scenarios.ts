import { addTask, firstTask, scenario } from "./ordered.ts";

export const addTwo = scenario(
  "Add two tasks and ask for the first task, which fails the output schema when the Bag visits the records in reverse order; test reports reversedException",
  {
    given: { start: "2026-10-25T09:00:00+09:00", records: { Task: [] }, peers: [] },
    when: (w) => {
      w.client.send(addTask, { taskId: "task-1" });
      w.client.send(addTask, { taskId: "task-2" });
      w.client.call(firstTask, {});
    },
    then: () => [],
  },
);
