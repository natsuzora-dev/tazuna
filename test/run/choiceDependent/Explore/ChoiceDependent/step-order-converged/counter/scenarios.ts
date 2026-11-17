import { addTask, scenario } from "./counter.ts";

export const addOne = scenario(
  "Add a task: the always guard of watcher reads the marks that mark adds, and the record change that mark makes evaluates the guard again, so in either order watcher ends in many; no violation",
  {
    given: { start: "2026-10-25T09:00:00+09:00", records: { Mark: [], Flag: { isOn: false } }, peers: {} },
    when: (w) => {
      w.client.send(addTask, { taskId: "task-1" });
    },
    then: () => [],
  },
);
