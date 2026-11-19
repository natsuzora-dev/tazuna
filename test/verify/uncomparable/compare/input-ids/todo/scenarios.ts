import { addTask, removeTask, scenario } from "./todo.ts";

export const resend = scenario(
  "Send addTask twice with one id; the implementation trace of this scenario gives the second line another id and answers the first id, so verify reports differentInput",
  {
    given: { start: "2026-10-25T00:00:00Z", records: {}, peers: [] },
    when: (w) => {
      const first = w.client.send(addTask, { taskId: "task-1" });
      w.client.send(addTask, { taskId: "task-1" }, { sameIdAs: first });
    },
    then: () => [],
  },
);

export const addAndRemove = scenario(
  "Add a task and remove it; the implementation trace of this scenario gives removeTask the id of addTask, so verify reports differentInput",
  {
    given: { start: "2026-10-25T00:00:00Z", records: {}, peers: [] },
    when: (w) => {
      w.client.send(addTask, { taskId: "task-1" });
      w.client.send(removeTask, { taskId: "task-1" });
    },
    then: () => [],
  },
);
