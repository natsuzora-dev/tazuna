import { at, mock, scenario, send } from "@natsuzora-dev/tazuna";
import { calendar } from "../calendar/contract.ts";
import { addTask, planner } from "./todo.ts";

const fromAdded = { input: { from: "2026-10-25T09:00:00+09:00" } };

export const answerEarly = scenario(
  "Answer the request that the planner sends for the added task, chosen by its input; no violation",
  [
    at("2026-10-25T09:00:00+09:00"),
    send(addTask, { taskId: "task-1", title: "Buy milk" }),
    mock(planner, [calendar.nextDay, { result: "fulfilled", output: { day: "2026-10-26T00:00:00+09:00" } }, fromAdded]),
  ],
);

export const answerOneOfTwo = scenario("Answer one of two questions; no violation", [
  at("2026-10-25T09:00:00+09:00"),
  send(addTask, { taskId: "task-1", title: "Buy milk" }),
  mock(planner, [
    calendar.nextDay,
    { result: "fulfilled", output: { day: "2026-10-26T00:00:00+09:00" } },
    { input: { from: "2026-10-25T10:00:00+09:00" } },
  ]),
]);

export const answerBeforeAsking = scenario(
  "Answer before the planner asks; no request waits for an answer, so test reports noWaitingRequest",
  [
    at("2026-10-25T09:00:00+09:00"),
    mock(planner, [calendar.nextDay, { result: "fulfilled", output: { day: "2026-10-26T00:00:00+09:00" } }]),
  ],
);

export const answerStaleWhileAsking = scenario(
  "Answer a stale request while the planner still asks; no request is stale yet, so test reports noStaleRequest",
  [
    at("2026-10-25T09:00:00+09:00"),
    send(addTask, { taskId: "task-1", title: "Buy milk" }),
    mock(planner, [
      calendar.nextDay,
      { result: "fulfilled", output: { day: "2026-10-26T00:00:00+09:00" } },
      { stale: true },
    ]),
  ],
);
