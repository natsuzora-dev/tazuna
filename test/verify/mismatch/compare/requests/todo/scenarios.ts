import { at, scenario, send } from "@natsuzora-dev/tazuna";
import { addTask } from "./todo.ts";

export const addHourly = scenario("Add a task every hour; no violation", [
  at("2026-10-25T00:00:00Z"),
  send(addTask, { taskId: "task-1", title: "Buy milk" }),
  at("2026-10-25T01:00:00Z"),
  send(addTask, { taskId: "task-2", title: "Buy eggs" }),
  at("2026-10-25T02:00:00Z"),
  send(addTask, { taskId: "task-3", title: "Buy tea" }),
]);

export const addHourlyWrongRequests = scenario(
  "Same inputs as addHourly; the implementation trace of this scenario sends calendar.nextDay with another input, misses the second one, and sends an extra calendar.book, so verify reports Mismatch.request, missingLine, and unexpectedLine",
  [
    at("2026-10-25T00:00:00Z"),
    send(addTask, { taskId: "task-1", title: "Buy milk" }),
    at("2026-10-25T01:00:00Z"),
    send(addTask, { taskId: "task-2", title: "Buy eggs" }),
    at("2026-10-25T02:00:00Z"),
    send(addTask, { taskId: "task-3", title: "Buy tea" }),
  ],
);
