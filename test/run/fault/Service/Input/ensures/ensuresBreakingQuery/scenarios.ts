import { at, call, scenario, send } from "@natsuzora-dev/tazuna";
import { addTask, taskCount } from "./todo.ts";

export const addTwo = scenario(
  "Add two tasks and count them; taskCount answers one more than the tasks and fails its ensures countsTasks, so test reports failedEnsures",
  [
    at("2026-10-25T09:00:00+09:00"),
    send(addTask, { taskId: "task-1", title: "milk" }),
    send(addTask, { taskId: "task-2", title: "eggs" }),
    call(taskCount, {}),
  ],
);
