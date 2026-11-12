import { at, scenario, send } from "@natsuzora-dev/tazuna";
import { addTask, openLabels, pressRemind, renameTask, selectTask } from "./todo.ts";

export const renamedWhileWatching = scenario(
  "Add a task, select it, rename it, and press remind; the held title of watcher is not a stored value but is computed from the current record by the holds expression each time it is read, so watcher notifies the first title when it enters watching and the new title when it reenters watching after the rename",
  [
    at("2026-10-25T10:00:00+09:00"),
    send(addTask, { taskId: "task-1", title: "Buy milk" }),
    send(selectTask, { taskId: "task-1" }),
    send(renameTask, { taskId: "task-1", title: "Buy eggs" }),
    send(pressRemind, {}),
  ],
);

export const sameNameInRegions = scenario(
  "Open the labels; an expression of labels reads only the held values of the state it is written in and of its ancestors, so the send of leftShowing notifies its own label, and the send of rightShowing, in another region of the parallel state, notifies its label of the same name. The assign of the transition out of leftShowing also reads the label of leftShowing",
  [at("2026-10-25T10:00:00+09:00"), send(openLabels, {})],
);
