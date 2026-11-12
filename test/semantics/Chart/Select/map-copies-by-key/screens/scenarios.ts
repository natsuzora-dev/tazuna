import { at, mock, operate, scenario } from "@natsuzora-dev/tazuna";
import { todo } from "../todo/contract.ts";
import { listScreen } from "./listScreen.ts";

const shown = (...taskIds: string[]) => mock(listScreen, [todo.tasks, { result: "fulfilled", output: { taskIds } }]);
const completed = (taskId: string) =>
  mock(listScreen, [todo.completeTask, { result: "accepted" }, { input: { taskId } }]);

export const routedByKey = scenario(
  "Show task-1 and task-2, complete task-1 twice and task-2 once, and answer; the operation complete reaches only the copy whose key taskId equals the taskId of the payload. The copy of task-1 does not accept a second complete while it waits in completing for the answer. listScreen accepts complete for task-2 while the copy of task-1 waits",
  [
    at("2026-10-25T10:00:00+09:00"),
    shown("task-1", "task-2"),
    operate(listScreen, "complete", { taskId: "task-1" }),
    operate(listScreen, "complete", { taskId: "task-1" }),
    operate(listScreen, "complete", { taskId: "task-2" }),
    completed("task-2"),
    completed("task-1"),
    operate(listScreen, "complete", { taskId: "task-1" }),
  ],
);

export const noCopyForKey = scenario(
  "Show task-1 and complete task-3; the operation complete for task-3, which has no copy, reaches no copy",
  [at("2026-10-25T10:00:00+09:00"), shown("task-1"), operate(listScreen, "complete", { taskId: "task-3" })],
);

export const withoutKeyFields = scenario(
  "Show two tasks and complete all; the operation completeAll, whose payload has no taskId, reaches every copy",
  [at("2026-10-25T10:00:00+09:00"), shown("task-1", "task-2"), operate(listScreen, "completeAll")],
);
