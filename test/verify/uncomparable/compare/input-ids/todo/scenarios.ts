import { at, scenario, send } from "@natsuzora-dev/tazuna";
import { addTask, removeTask } from "./todo.ts";

export const resend = scenario(
  "Send addTask twice with one id; the implementation trace of this scenario gives the second line another id and answers the first id, so verify reports differentInput",
  [
    at("2026-10-25T00:00:00Z"),
    send(addTask, { taskId: "task-1" }, { id: "c1" }),
    send(addTask, { taskId: "task-1" }, { id: "c1" }),
  ],
);

export const addAndRemove = scenario(
  "Add a task and remove it; the implementation trace of this scenario gives removeTask the id of addTask, so verify reports differentInput",
  [at("2026-10-25T00:00:00Z"), send(addTask, { taskId: "task-1" }), send(removeTask, { taskId: "task-1" })],
);
