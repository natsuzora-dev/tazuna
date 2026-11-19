import { addTask, scenario } from "./todo.ts";

export const addTwice = scenario(
  "Add two tasks; todo sends every output of the first addTask, including the events of the commands that logAdded, countAdded, and scheduler send to their own service, before it processes the second addTask. The queue processes the earliest queued command first, so the archive that archiveLogged queues on the logged of log comes after the count queued before it",
  {
    given: { start: "2026-10-25T09:00:00+09:00", records: {}, peers: [] },
    when: (w) => {
      w.client.send(addTask, { taskId: "task-1" });
      w.client.send(addTask, { taskId: "task-2" });
    },
    then: () => [],
  },
);
