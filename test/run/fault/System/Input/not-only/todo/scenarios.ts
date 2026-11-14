import { at, call, scenario, send } from "@natsuzora-dev/tazuna";
import { addTask, taskNamed } from "./todo.ts";

export const askShared = scenario(
  "Add two tasks with one title and ask for the task of that title; only() finds two, so test reports notOnly",
  [
    at("2026-10-25T09:00:00+09:00"),
    send(addTask, { taskId: "task-1", title: "Buy milk" }),
    send(addTask, { taskId: "task-2", title: "Buy milk" }),
    call(taskNamed, { title: "Buy milk" }),
  ],
);
