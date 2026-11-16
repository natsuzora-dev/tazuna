import { addTask, scenario } from "./todo.ts";

export const addTwice = scenario(
  "Add a task at 10:00 and another at 10:30; todo sends every output of the first addTask at 10:00, including the events of log that logAdded sends, before it processes the second addTask. The now that the decide of log reads is also the time at which addTask arrived",
  {
    given: { start: "2026-10-25T10:00:00+09:00", records: {}, peers: {} },
    when: (w) => {
      w.client.send(addTask, { taskId: "task-1" });
      w.clock.at("2026-10-25T10:30:00+09:00");
      w.client.send(addTask, { taskId: "task-2" });
    },
    then: () => [],
  },
);
