import { at, call, scenario, send, subscribe } from "@natsuzora-dev/tazuna";
import { addTask, taskTitles } from "./todo.ts";

export const watchTitles = scenario("Subscribe to the titles, add two tasks, and ask for the titles; no violation", [
  at("2026-10-25T00:00:00Z"),
  subscribe(taskTitles, {}),
  send(addTask, { taskId: "task-1", title: "Buy milk" }),
  send(addTask, { taskId: "task-2", title: "Buy eggs" }),
  call(taskTitles, {}),
]);

export const watchTitlesWrongAnswers = scenario(
  "Same inputs as watchTitles; the implementation trace of this scenario answers the subscription with other titles, misses an answer, and sends an extra one, so verify reports Mismatch.output, missingAnswer, and unexpectedLine",
  [
    at("2026-10-25T00:00:00Z"),
    subscribe(taskTitles, {}),
    send(addTask, { taskId: "task-1", title: "Buy milk" }),
    send(addTask, { taskId: "task-2", title: "Buy eggs" }),
    call(taskTitles, {}),
  ],
);
