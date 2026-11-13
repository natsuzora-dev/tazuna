import { at, scenario, send } from "@natsuzora-dev/tazuna";
import { addTask, forget } from "./todo.ts";

export const forgetFirst = scenario(
  "Add two tasks and forget the first seen task; the implementation trace of this scenario creates the seen keys in the other order and gives the snapshot's key verbatim, which is the implementation's key of the second task, so verify reports differentInput",
  [
    at("2026-10-25T00:00:00Z"),
    send(addTask, { taskId: "task-1" }),
    send(addTask, { taskId: "task-2" }),
    send(forget, { id: "Seen-1" }),
  ],
);

export const forgetOne = scenario(
  "Add a task and forget its seen task; the implementation trace of this scenario gives the snapshot's key verbatim instead of the key that the implementation created, so verify reports differentInput",
  [at("2026-10-25T00:00:00Z"), send(addTask, { taskId: "task-1" }), send(forget, { id: "Seen-1" })],
);
