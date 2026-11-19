import { scenario, taskTitle } from "./todo.ts";

export const askMissing = scenario({
  description: "Ask taskTitle for the title of a missing task; its resolve throws a string, so test reports exception",
  given: { start: "2026-10-25T09:00:00+09:00", records: { Task: [] }, peers: [] },
  when: (w) => {
    w.client.call(taskTitle, { taskId: "task-9" });
  },
  then: () => [],
});
