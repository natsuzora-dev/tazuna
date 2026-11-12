import { at, call, scenario, send } from "@natsuzora-dev/tazuna";
import { addTask, taskTitles } from "./todo.ts";

export const addTwo = scenario(
  "Add two tasks and list them; taskTitles answers them in reverse order and fails its ensures sorted, so test reports failedEnsures",
  [
    at("2026-10-25T09:00:00+09:00"),
    send(addTask, { taskId: "task-1", title: "milk" }),
    send(addTask, { taskId: "task-2", title: "eggs" }),
    call(taskTitles, {}),
  ],
);
