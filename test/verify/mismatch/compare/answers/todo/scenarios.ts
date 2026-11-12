import { at, call, scenario, send } from "@natsuzora-dev/tazuna";
import { addTask, completeTask, taskCard, taskTitles } from "./todo.ts";

export const answers = scenario(
  "Add a task twice, complete a missing task, list the titles, and complete the task; no violation",
  [
    at("2026-10-25T00:00:00Z"),
    send(addTask, { taskId: "task-1", title: "Buy milk" }),
    send(addTask, { taskId: "task-1", title: "Buy eggs" }),
    send(completeTask, { taskId: "task-9" }),
    call(taskTitles, {}),
    send(completeTask, { taskId: "task-1" }),
  ],
);

export const answersWrongResults = scenario(
  "Add a task twice, complete a missing task, list the titles, complete the task, and add another task; the implementation trace of this scenario answers with other results, rejection kinds, and outputs, so verify reports Mismatch.result, Mismatch.rejection, Mismatch.output, missingAnswer, and unexpectedLine",
  [
    at("2026-10-25T00:00:00Z"),
    send(addTask, { taskId: "task-1", title: "Buy milk" }),
    send(addTask, { taskId: "task-1", title: "Buy eggs" }),
    send(completeTask, { taskId: "task-9" }),
    call(taskTitles, {}),
    send(completeTask, { taskId: "task-1" }),
    send(addTask, { taskId: "task-2", title: "Buy eggs" }),
  ],
);

export const showCards = scenario(
  "Ask for the task card three times; the implementation trace of this scenario answers with an unknown field, another part name, and another time, so verify reports Mismatch.output",
  [at("2026-10-25T00:00:00Z"), call(taskCard, {}), call(taskCard, {}), call(taskCard, {})],
);
