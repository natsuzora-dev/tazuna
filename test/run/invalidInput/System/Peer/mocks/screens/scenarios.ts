import { at, elsewhere, mock, scenario, send } from "@natsuzora-dev/tazuna";
import { todo } from "../todo/contract.ts";
import { listScreen } from "./screens.ts";

const milkShown = mock(listScreen, [todo.taskTitles, { result: "fulfilled", output: { titles: ["Buy milk"] } }]);
const fromMilk = { given: { todo: todo.states.milk } };

export const showsGiven = scenario(
  "Answer the titles of the given state of todo, then of the task that another caller adds; no violation",
  [
    at("2026-10-25T10:00:00+09:00"),
    milkShown,
    elsewhere(todo, send(todo.addTask, { taskId: "task-2", title: "Buy bread" })),
    mock(listScreen, [todo.taskTitles, { result: "fulfilled", output: { titles: ["Buy milk", "Buy bread"] } }]),
  ],
  fromMilk,
);

export const showsMissingTask = scenario(
  "Answer a title although todo starts with no task; todo answers no title, so test reports unproducibleAnswer",
  [at("2026-10-25T10:00:00+09:00"), milkShown],
);

export const showsSameTitlesAgain = scenario(
  "Answer the same titles twice; todo answers a subscription again only when the answer changes, so test reports unansweredRequest",
  [at("2026-10-25T10:00:00+09:00"), milkShown, milkShown],
  fromMilk,
);

export const addsCreatedKeyElsewhere = scenario(
  "Let another caller add a task whose key has the form of a createKey value of todo; todo halts on the input with uncreatedKey, so test reports haltedPeer",
  [
    at("2026-10-25T10:00:00+09:00"),
    elsewhere(todo, send(todo.addTask, { taskId: "Task-1", title: "Buy bread" })),
    milkShown,
  ],
  fromMilk,
);
