import { at, cannotOperate, mock, operate, scenario } from "@natsuzora-dev/tazuna";
import { todo } from "../todo/contract.ts";
import { rowScreen } from "./rowScreen.ts";

export const offersPerCopy = scenario(
  "Show task-1 and task-2 and complete them; rowScreen evaluates offers per copy. While the copies of task-1 and task-2 are in idle, it accepts complete for both taskIds. When the copy of task-1 enters completing, its offers return [], so rowScreen does not accept complete for task-1 but still accepts it for task-2",
  [
    at("2026-10-25T10:00:00+09:00"),
    mock(rowScreen, [todo.openTasks, { result: "fulfilled", output: { taskIds: ["task-1", "task-2"] } }]),
    operate(rowScreen, "complete", { taskId: "task-1" }),
    cannotOperate(rowScreen, "complete", { taskId: "task-1" }),
    operate(rowScreen, "complete", { taskId: "task-2" }),
  ],
);
