import { at, scenario, send } from "@natsuzora-dev/tazuna";
import { addTask, pickFirstTask } from "./todo.ts";

export const pickByCodePoint = scenario(
  "Add a task keyed U+FF61 and a task keyed U+1F600 and pick the first task; decide reads the keys in code-point order, so firstTaskPicked names U+FF61, which comes after U+1F600 in UTF-16 code-unit order",
  [
    at("2026-10-25T10:00:00+09:00"),
    send(addTask, { taskId: "｡" }),
    send(addTask, { taskId: "\u{1F600}" }),
    send(pickFirstTask, {}),
  ],
);
