import { at, mock, scenario, send } from "@natsuzora-dev/tazuna";
import { calendar } from "../calendar/contract.ts";
import { addTask, planner } from "./todo.ts";

export const addOne = scenario("Add one task; verify reports unexpectedInput", [
  at("2026-10-25T00:00:00Z"),
  send(addTask, { taskId: "task-1", title: "Buy milk" }),
]);

export const addTwo = scenario("Add two tasks; verify reports missingInput", [
  at("2026-10-25T00:00:00Z"),
  send(addTask, { taskId: "task-1", title: "Buy milk" }),
  send(addTask, { taskId: "task-2", title: "Buy eggs" }),
]);

export const addMilk = scenario("Add a task to buy milk; verify reports differentInput", [
  at("2026-10-25T00:00:00Z"),
  send(addTask, { taskId: "task-1", title: "Buy milk" }),
]);

export const answerDay = scenario("Add a task and answer the next day; verify reports differentRequest", [
  at("2026-10-25T00:00:00Z"),
  send(addTask, { taskId: "task-1", title: "Buy milk" }),
  mock(planner, [calendar.nextDay, { result: "fulfilled", output: { day: "2026-10-26T00:00:00Z" } }]),
]);
