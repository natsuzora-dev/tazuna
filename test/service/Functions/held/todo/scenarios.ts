import { addTask, given, openLabels, pressRemind, renameTask, scenario, selectTask } from "./todo.ts";

const arranged = given({ start: "2026-10-25T10:00:00+09:00", records: { Task: [] }, peers: [] });

export const renamedWhileWatching = scenario({
  description:
    "Add a task, select it, rename it, and press remind; the edge into watching stores the title for the visit, so after the rename the guard still reads the first title and sees the rename, and watcher notifies the first title when it enters watching and the new title when it enters watching again",
  given: arranged,
  when: (w) => {
    w.client.send(addTask, { taskId: "task-1", title: "Buy milk" });
    w.client.send(selectTask, { taskId: "task-1" });
    w.client.send(renameTask, { taskId: "task-1", title: "Buy eggs" });
    w.client.send(pressRemind, {});
  },
  then: () => [],
});

export const sameNameInRegions = scenario({
  description:
    "Open the labels; the initial edge of each region fills the label of its initial state, and an expression reads only the parameters of the state it is written in, so the send of leftShowing notifies its own label, and the send of rightShowing, in another region of the parallel state, notifies its label of the same name. The assign of the transition out of leftShowing, which runs after leftShowing exits, also reads the label of leftShowing",
  given: arranged,
  when: (w) => {
    w.client.send(openLabels, {});
  },
  then: () => [],
});
