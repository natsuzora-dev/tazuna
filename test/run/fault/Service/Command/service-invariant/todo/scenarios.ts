import { parseInstant } from "@natsuzora-dev/tazuna";
import { addTask, scenario } from "./todo.ts";

export const addDue = scenario({
  description:
    "Add a task due 2026-10-25; the service invariant moves the date three million days on, past year 9999, so addDays faults and test reports exception located at the service",
  given: { start: parseInstant("2026-10-25T09:00:00+09:00"), records: { Task: [] }, peers: [] },
  when: (w) => {
    w.client.send(addTask, { taskId: "task-1", due: "2026-10-25" });
  },
  then: () => [],
});
