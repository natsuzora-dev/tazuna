import { parseInstant } from "@natsuzora-dev/tazuna";
import { addTask, scenario } from "./backlog.ts";

export const work = scenario({
  description:
    "Add one task and nothing else. The id domain holds only its id, so the paths that test appends complete the task but add no second one, completeTask always finds the task (bindsRejection), and progress never leaves done or sees allDone false, and titleWatcher never leaves seen; the title Buy milk passes both guards of the first transition from idle, so its second transition is never taken. No transition enters archived. test reports transition, guardFalse, and state",
  given: { start: parseInstant("2026-10-25T09:00:00+09:00"), records: { Task: [] }, peers: [] },
  when: (w) => {
    w.client.send(addTask, { taskId: "task-1", title: "Buy milk" });
  },
  then: () => [],
});
