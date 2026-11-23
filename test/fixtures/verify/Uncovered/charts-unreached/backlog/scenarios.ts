import { parseInstant } from "@natsuzora-dev/tazuna";
import { addTask, scenario } from "./backlog.ts";

export const work = scenario({
  description:
    "Add one task and nothing else. No trace completes a task, so progress never leaves busy and titleWatcher never leaves seen; the title Buy milk passes both guards of the first transition from idle, so its second transition is never taken, and no transition enters archived. verify --coverage reports request, transition, guardFalse, and state",
  given: { start: parseInstant("2026-10-25T09:00:00+09:00"), records: { Task: [] }, peers: [] },
  when: (w) => {
    w.client.as("client").send(addTask, { taskId: "task-1", title: "Buy milk" });
  },
  then: () => [],
});
