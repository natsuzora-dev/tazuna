import { parseInstant } from "@natsuzora-dev/tazuna";
import { dueAfter, scenario, taskTitle } from "./todo.ts";

export const askMissing = scenario({
  description: "Ask for the title of a missing task; taskTitle answers null; no violation",
  given: { start: parseInstant("2026-10-25T09:00:00+09:00"), records: { Task: [] }, peers: [] },
  when: (w) => {
    w.client.call(taskTitle, { taskId: "task-9" });
  },
  then: () => [],
});

export const askFarDue = scenario({
  description: "Ask for a due date past year 9999; addDays throws; Fault.exception",
  given: { start: parseInstant("2026-10-25T09:00:00+09:00"), records: { Task: [] }, peers: [] },
  when: (w) => {
    w.client.call(dueAfter, { from: "2026-10-25", days: 3_000_000 });
  },
  then: () => [],
});
