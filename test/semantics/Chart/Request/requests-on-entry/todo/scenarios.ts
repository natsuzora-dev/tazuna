import { at, mock, scenario, send } from "@natsuzora-dev/tazuna";
import { calendar } from "../calendar/contract.ts";
import { dayNoter } from "./machines.ts";
import { addDoneTask, addTask, completeTask } from "./todo.ts";

export const answerAfterExit = scenario(
  "Add a task, complete it, answer, add another task, and answer; dayNoter sends calendar.nextDay each time it enters asking. The answer to the first request arrives after completeTask has made dayNoter exit asking, so it takes no transition. The answer to the second request moves dayNoter to noting, which records the next day",
  [
    at("2026-10-25T10:00:00+09:00"),
    send(addTask, { taskId: "task-1" }),
    send(completeTask, { taskId: "task-1" }),
    mock(dayNoter, [
      calendar.nextDay,
      { result: "fulfilled", output: { day: "2026-10-26T00:00:00+09:00" } },
      { stale: true },
    ]),
    send(addTask, { taskId: "task-2" }),
    mock(dayNoter, [calendar.nextDay, { result: "fulfilled", output: { day: "2026-10-26T00:00:00+09:00" } }]),
  ],
);

export const passThrough = scenario(
  "Add a done task; in the one message of addDoneTask, dayNoter enters asking on taskAdded and exits it on taskCompleted. It is not in asking at the end of the macrostep, so it sends no calendar.nextDay",
  [at("2026-10-25T10:00:00+09:00"), send(addDoneTask, { taskId: "task-1" })],
);
