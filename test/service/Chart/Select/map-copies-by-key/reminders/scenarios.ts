import { clearAll, scenario, starTask } from "./reminders.ts";

const given = { start: "2026-10-25T10:00:00+09:00", records: {}, peers: {} } as const;

export const eventRoutedByKey = scenario(
  "Star task-1 and task-3; taskStarred reaches only the copy whose key taskId equals the taskId of the payload, so only the copy of task-1 notifies, and the taskStarred of task-3, which has no copy, reaches no copy",
  {
    given,
    when: (w) => {
      w.client.send(starTask, { taskId: "task-1" });
      w.client.send(starTask, { taskId: "task-3" });
    },
    then: () => [],
  },
);

export const eventWithoutKeyFields = scenario(
  "Clear all; allCleared, whose payload has no taskId, reaches every copy",
  {
    given,
    when: (w) => {
      w.client.send(clearAll, {});
    },
    then: () => [],
  },
);
