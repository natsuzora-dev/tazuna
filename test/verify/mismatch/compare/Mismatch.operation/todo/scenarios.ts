import { addTask, scenario } from "./todo.ts";

export const addOneOperated = scenario({
  description: "Add a task and open its screen; the implementation trace opens the screen of another task",
  given: { start: "2026-10-25T00:00:00Z", records: {}, peers: [] },
  when: (w) => {
    w.client.send(addTask, { taskId: "task-1" });
  },
  then: () => [],
});
