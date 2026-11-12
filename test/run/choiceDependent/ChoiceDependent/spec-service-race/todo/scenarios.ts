import { at, mock, scenario, send } from "@natsuzora-dev/tazuna";
import { stats } from "../stats/contract.ts";
import { closer, closeTask, completer, completeTask } from "./todo.ts";

export const completeOne = scenario(
  "Complete a task: counting reads isCounting, which resuming writes, but both orders give the same outputs; no violation",
  [
    at("2026-10-25T09:00:00+09:00"),
    send(completeTask, { taskId: "task-1" }),
    mock(completer, [stats.countCompleted, { result: "accepted" }]),
    mock(completer, [stats.resumeCounting, { result: "accepted" }]),
  ],
);

export const closeOne = scenario(
  "Close a task; counting writes the completed count, which resetting also writes, so the records depend on which request stats receives first, so test reports requestOrder",
  [
    at("2026-10-25T09:00:00+09:00"),
    send(closeTask, { taskId: "task-1" }),
    mock(closer, [stats.countCompleted, { result: "accepted" }]),
    mock(closer, [stats.resetCount, { result: "accepted" }]),
  ],
);
