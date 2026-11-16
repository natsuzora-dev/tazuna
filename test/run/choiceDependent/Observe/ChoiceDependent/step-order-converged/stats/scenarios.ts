import { addTask, scenario } from "./stats.ts";

export const addOne = scenario(
  "Add a task: countAdded and rememberTitle both write the whole Stats record from the record they read, so in either order Stats counts the task and remembers its title; no violation",
  {
    given: { start: "2026-10-25T09:00:00+09:00", records: { Task: [], Stats: { added: 0, lastTitle: "" } }, peers: {} },
    when: (w) => {
      w.client.send(addTask, { taskId: "task-1", title: "Buy milk" });
    },
    then: () => [],
  },
);
