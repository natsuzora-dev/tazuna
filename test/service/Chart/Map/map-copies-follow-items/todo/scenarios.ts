import { at, mock, scenario, send } from "@natsuzora-dev/tazuna";
import { calendar } from "../calendar/contract.ts";
import { dayNoter } from "./machines.ts";
import { addTask, completeTask, reopenTask } from "./todo.ts";

export const copiesFollowItems = scenario(
  "Add task-1 and task-2, complete task-1, and reopen it; dayNoter runs a copy for each added task and asks calendar for the next day in each copy. Completing task-1 removes it from items, so its copy exits its states and the answer to its request is stale. Reopening task-1 makes dayNoter run a new copy of task-1, which asks calendar again",
  [
    at("2026-10-25T10:00:00Z"),
    send(addTask, { taskId: "task-1" }),
    at("2026-10-25T10:05:00Z"),
    send(addTask, { taskId: "task-2" }),
    send(completeTask, { taskId: "task-1" }),
    mock(dayNoter, [
      calendar.nextDay,
      { result: "fulfilled", output: { day: "2026-10-26T00:00:00Z" } },
      { stale: true },
    ]),
    send(reopenTask, { taskId: "task-1" }),
    mock(dayNoter, [
      calendar.nextDay,
      { result: "fulfilled", output: { day: "2026-10-27T00:00:00Z" } },
      { input: { from: "2026-10-25T10:05:00Z", taskId: "task-2" } },
    ]),
    mock(dayNoter, [calendar.nextDay, { result: "fulfilled", output: { day: "2026-10-28T00:00:00Z" } }]),
  ],
);
