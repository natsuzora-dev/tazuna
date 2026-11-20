import { addTask, scenario } from "./todo.ts";

export const loggedBeforeAnswer = scenario({
  description:
    "Add a task; logger enters logging and sends the log command to its own service. log emits logged, on which logger leaves logging before the queue delivers the acceptance of log. The queued log is stale, so its acceptance only ends the wait: logger takes no onAccepted and sends no note",
  given: { start: "2026-10-25T10:00:00+09:00", records: {}, peers: [] },
  when: (w) => {
    w.client.send(addTask, { taskId: "task-1" });
  },
  then: () => [],
});
