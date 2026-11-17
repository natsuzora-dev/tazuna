import { addTask, scenario } from "./latest.ts";

export const rememberOne = scenario(
  "Add a task; both regions of tracker assign lastTaskId in one microstep, so the result depends on their order, so test reports bothAssign",
  {
    given: { start: "2026-10-25T09:00:00+09:00", records: {}, peers: {} },
    when: (w) => {
      w.client.send(addTask, { taskId: "task-1" });
    },
    then: () => [],
  },
);
