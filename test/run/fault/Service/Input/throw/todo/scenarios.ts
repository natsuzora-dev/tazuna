import { scenario, taskTitle } from "./todo.ts";

export const askMissing = scenario("Ask for the title of a missing task; taskTitle answers null; no violation", {
  given: { start: "2026-10-25T09:00:00+09:00", records: { Task: [] }, peers: [] },
  when: (w) => {
    w.client.call(taskTitle, { taskId: "task-9" });
  },
  then: () => [],
});
