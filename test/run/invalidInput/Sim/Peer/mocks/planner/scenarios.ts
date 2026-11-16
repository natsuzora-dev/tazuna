import { at, mock, receive, scenario, send } from "@natsuzora-dev/tazuna";
import { todo } from "../todo/contract.ts";
import { addPlanned, plan } from "./planner.ts";

const milkAdded = mock(addPlanned, [todo.addTask, { result: "accepted" }]);
const breadAdded = mock(addPlanned, [todo.addTask, { result: "accepted" }]);

export const linksAddedToItsRequest = scenario(
  "Plan milk and bread, and receive taskAdded for milk as the result of the milk request; no violation",
  [
    at("2026-10-25T10:00:00+09:00"),
    send(plan, { taskId: "task-1", title: "Buy milk" }),
    milkAdded,
    send(plan, { taskId: "task-2", title: "Buy bread" }),
    breadAdded,
    receive(todo.taskAdded, { taskId: "task-1" }, { resultOf: milkAdded }),
  ],
);

export const linksAddedToOtherRequest = scenario(
  "Plan milk and bread, and receive taskAdded for milk as the result of the bread request; todo emits it as the result of the milk request, so test reports unproducibleEvent",
  [
    at("2026-10-25T10:00:00+09:00"),
    send(plan, { taskId: "task-1", title: "Buy milk" }),
    milkAdded,
    send(plan, { taskId: "task-2", title: "Buy bread" }),
    breadAdded,
    receive(todo.taskAdded, { taskId: "task-1" }, { resultOf: breadAdded }),
  ],
);
