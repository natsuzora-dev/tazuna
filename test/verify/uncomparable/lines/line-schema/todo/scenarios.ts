import { at, scenario, send } from "@natsuzora-dev/tazuna";
import { addTask } from "./todo.ts";

export const addTwoCut = scenario(
  "Add two tasks; the trace has a line that the trace line schema cannot read after the second request, so verify reports that line and compares no line after the second request",
  [
    at("2026-10-25T00:00:00Z"),
    send(addTask, { taskId: "task-1", title: "Buy milk" }),
    send(addTask, { taskId: "task-2", title: "Buy eggs" }),
  ],
);
