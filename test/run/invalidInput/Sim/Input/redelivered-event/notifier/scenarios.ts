import { at, elsewhere, receive, scenario, send, unchecked } from "@natsuzora-dev/tazuna";
import { todo } from "../todo/contract.ts";

export const seeTwice = scenario(
  "Receive an event again with the same id and another task; test reports changedRedeliveryPayload",
  [
    at("2026-10-25T09:00:00+09:00"),
    elsewhere(todo, send(todo.addTask, { taskId: "task-1" })),
    elsewhere(todo, send(todo.addTask, { taskId: "task-2" })),
    receive(todo.taskAdded, { taskId: "task-1" }, { id: "e9" }),
    receive(todo.taskAdded, { taskId: "task-2" }, { id: "e9" }),
  ],
);

export const reuseId = scenario(
  "Receive a taskRemoved event with the id of a taskAdded event; test reports reusedEventId",
  [
    at("2026-10-25T09:00:00+09:00"),
    elsewhere(todo, send(todo.addTask, { taskId: "task-1" })),
    elsewhere(todo, send(todo.removeTask, { taskId: "task-1" })),
    receive(todo.taskAdded, { taskId: "task-1" }, { id: "e9" }),
    receive(todo.taskRemoved, { taskId: "task-1" }, { id: "e9" }),
  ],
);

export const seeMalformedAgain = scenario(
  "Receive an event again with the same id and a payload that does not match the schema; the check for the id comes first and the run goes on to the next event, so test reports changedRedeliveryPayload",
  [
    at("2026-10-25T09:00:00+09:00"),
    elsewhere(todo, send(todo.addTask, { taskId: "task-1" })),
    elsewhere(todo, send(todo.addTask, { taskId: "task-2" })),
    receive(todo.taskAdded, { taskId: "task-1" }, { id: "e9" }),
    receive(todo.taskAdded, { taskId: unchecked(1) }, { id: "e9" }),
    receive(todo.taskAdded, { taskId: "task-2" }, { id: "e10" }),
  ],
);
