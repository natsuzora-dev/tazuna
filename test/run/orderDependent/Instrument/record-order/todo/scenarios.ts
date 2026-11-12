import { at, call, scenario, send } from "@natsuzora-dev/tazuna";
import { addTask, titles, titlesInArray } from "./todo.ts";

export const addTwo = scenario("Add two tasks and read their titles; no violation", [
  at("2026-10-25T09:00:00+09:00"),
  send(addTask, { taskId: "task-1", title: "Buy milk" }),
  send(addTask, { taskId: "task-2", title: "Buy eggs" }),
  call(titles, {}),
]);

export const addTwoAndReadArray = scenario(
  "Add two tasks and read their titles as an array in record order; the output changes when the records come in reverse key order, so test reports reversedRecords",
  [
    at("2026-10-25T09:00:00+09:00"),
    send(addTask, { taskId: "task-1", title: "Buy milk" }),
    send(addTask, { taskId: "task-2", title: "Buy eggs" }),
    call(titlesInArray, {}),
  ],
);
