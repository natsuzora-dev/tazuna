import { at, scenario, send } from "@natsuzora-dev/tazuna";
import { addTask } from "./todo.ts";

export const addTwo = scenario(
  "Add two tasks; addTask writes the titles in upper case and fails its ensures keepsTitle, so test reports failedEnsures",
  [
    at("2026-10-25T09:00:00+09:00"),
    send(addTask, { taskId: "task-1", title: "milk" }),
    send(addTask, { taskId: "task-2", title: "eggs" }),
  ],
);
