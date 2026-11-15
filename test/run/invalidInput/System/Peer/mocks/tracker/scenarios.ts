import { at, mock, receive, scenario } from "@natsuzora-dev/tazuna";
import { todo } from "../todo/contract.ts";
import { completeReported } from "./tracker.ts";

export const completesOnItsOwnReport = scenario(
  "Receive taskCompleted for task-1 and, on it, complete task-1 at the same time; todo emits taskCompleted only for that request, which tracker sends after it receives the event, so test reports unproducibleEvent",
  [
    at("2026-10-25T10:00:00+09:00"),
    receive(todo.taskCompleted, { taskId: "task-1" }),
    mock(completeReported, [todo.completeTask, { result: "accepted" }]),
  ],
  { given: { todo: todo.states.milk } },
);
