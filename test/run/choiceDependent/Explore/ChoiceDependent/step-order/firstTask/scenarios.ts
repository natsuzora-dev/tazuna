import { addTasks, scenario } from "./firstTask.ts";

export const addTwo = scenario(
  "Add two tasks in one group; remember takes the one it receives first, and the group has no order, so test reports stepOrder",
  {
    given: { start: "2026-10-25T09:00:00+09:00", records: { Flag: { by: "" } }, peers: {} },
    when: (w) => {
      w.client.send(addTasks, { taskIds: ["task-1", "task-2"] });
    },
    then: () => [],
  },
);
