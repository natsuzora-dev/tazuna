import { addTask, checkFirst, rankTasks, scenario } from "./tasks.ts";

export const addTwoAndRank = scenario(
  "Add two tasks, rank them and check the first; noteEveryTask creates a note key per task from a Bag callback, which test compares up to a renaming of the created keys and does not report, while the assign of tracker, the decide of rankTasks and the requires of checkFirst read the visiting order through a closure, so test reports reversedResult for each",
  {
    given: { start: "2026-10-25T09:00:00+09:00", records: { Task: [], Note: [] }, peers: [] },
    when: (w) => {
      w.client.send(addTask, { taskId: "task-1", title: "Buy milk" });
      w.client.send(addTask, { taskId: "task-2", title: "Buy eggs" });
      w.client.send(rankTasks, {});
      w.client.send(checkFirst, {});
    },
    then: () => [],
  },
);
