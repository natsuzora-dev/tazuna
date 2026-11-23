import { answered, fulfilled, parseInstant } from "@natsuzora-dev/tazuna";
import { addTask, hasTasks, isLate, scenario, taskCount, taskIds } from "./todo.ts";

export const subscribed = scenario({
  description:
    "Subscribe three times, add a task, unsubscribe from taskIds, and add another task; each time todo finishes processing addTask, it sends one answer line for each subscription whose answer changed. It sends no answer to the subscription to hasTasks, whose answer does not change, or to the ended subscription to taskIds",
  given: { start: parseInstant("2026-10-25T09:00:00+09:00"), records: { Task: [] }, peers: [] },
  when: (w) => {
    const ids = w.client.as("client").subscribe(taskIds, {});
    w.client.as("client").subscribe(taskCount, {});
    w.client.as("client").subscribe(hasTasks, {});
    w.client.as("client").send(addTask, { taskId: "task-1" });
    w.client.unsubscribe(ids);
    w.client.as("client").send(addTask, { taskId: "task-2" });
  },
  then: () => [],
});

export const answerChangesWithTime = scenario({
  description:
    "Subscribe to isLate at 09:00 and move the clock to 12:00; the answer changes at 11:00, so todo sends it after the time line",
  given: { start: parseInstant("2026-10-25T09:00:00+09:00"), records: { Task: [] }, peers: [] },
  when: (w) => {
    const late = w.client.as("client").subscribe(isLate, {});
    w.clock.at(parseInstant("2026-10-25T12:00:00+09:00"));
    return { late };
  },
  then: ({ late }) => [answered(late, [fulfilled({ late: false }), fulfilled({ late: true })])],
});
