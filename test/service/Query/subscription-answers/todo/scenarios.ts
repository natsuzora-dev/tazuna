import { answered } from "@natsuzora-dev/tazuna";
import { addTask, hasTasks, isLate, scenario, taskCount, taskIds } from "./todo.ts";

export const subscribed = scenario(
  "Subscribe three times, add a task, unsubscribe from taskIds, and add another task; each time todo finishes processing addTask, it sends one answer line for each subscription whose answer changed. It sends no answer to the subscription to hasTasks, whose answer does not change, or to the ended subscription to taskIds",
  {
    given: { start: "2026-10-25T09:00:00+09:00", records: { Task: [] }, peers: {} },
    when: (w) => {
      const ids = w.client.subscribe(taskIds, {});
      w.client.subscribe(taskCount, {});
      w.client.subscribe(hasTasks, {});
      w.client.send(addTask, { taskId: "task-1" });
      w.client.unsubscribe(ids);
      w.client.send(addTask, { taskId: "task-2" });
    },
    then: () => [],
  },
);

export const answerChangesWithTime = scenario(
  "Subscribe to isLate at 09:00 and move the clock to 12:00; the answer changes at 11:00, so todo sends it after the time line",
  {
    given: { start: "2026-10-25T09:00:00+09:00", records: { Task: [] }, peers: {} },
    when: (w) => {
      const late = w.client.subscribe(isLate, {});
      w.clock.at("2026-10-25T12:00:00+09:00");
      return { late };
    },
    then: ({ late }) => [
      answered(late, [
        { result: "fulfilled", output: { late: false } },
        { result: "fulfilled", output: { late: true } },
      ]),
    ],
  },
);
