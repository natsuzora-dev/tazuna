import { at, scenario, send } from "@natsuzora-dev/tazuna";
import { addTask } from "./todo.ts";

export const addOne = scenario(
  "Add a task; traces/todo/addOne.jsonl pairs with this snapshot, while traces/other/addOne.jsonl names no service of the spec, so verify reports unknownService",
  [at("2026-10-25T00:00:00Z"), send(addTask, { taskId: "task-1", title: "Buy milk" })],
);
