import { at, call, scenario, send } from "@natsuzora-dev/tazuna";
import { addTask, firstTask } from "./ordered.ts";

export const addTwo = scenario(
  "Add two tasks and ask for the first task, which fails the output schema when the Bag visits the records in reverse order; test reports reversedException",
  [
    at("2026-10-25T09:00:00+09:00"),
    send(addTask, { taskId: "task-1" }),
    send(addTask, { taskId: "task-2" }),
    call(firstTask, {}),
  ],
);
