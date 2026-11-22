import { parseInstant } from "@natsuzora-dev/tazuna";
import { addTask, scenario } from "./echo.ts";

export const addTwo = scenario({
  description:
    "Add two tasks: each message passes a chain of 100 commands, and the count of the chain starts again for the second message; no violation",
  given: { start: parseInstant("2026-10-25T09:00:00+09:00"), records: {}, peers: [] },
  when: (w) => {
    w.client.send(addTask, { taskId: "task-1" });
    w.client.send(addTask, { taskId: "task-2" });
  },
  then: () => [],
});
