import { at, elsewhere, mock, operate, scenario, subscribe, unsubscribe } from "@natsuzora-dev/tazuna";
import { todo } from "../todo/contract.ts";
import { boardScreen } from "./board.ts";

export const completesRenamedTask = scenario(
  "Name the tasks that todo created T-milk and T-bread, and complete T-bread; a mock may name the keys that todo creates with any strings, so todo completes the key that T-bread names and test reports nothing",
  [
    at("2026-10-25T10:00:00+09:00"),
    mock(boardScreen, [
      todo.tasks,
      {
        result: "fulfilled",
        output: {
          tasks: [
            { taskId: "T-milk", title: "Buy milk" },
            { taskId: "T-bread", title: "Buy bread" },
          ],
        },
      },
    ]),
    operate(boardScreen, "complete", { taskId: "T-bread" }),
    mock(boardScreen, [todo.completeTask, { result: "accepted" }]),
  ],
  { given: { todo: todo.states.milkAndBread } },
);

export const completesNamedTask = scenario(
  "Show and complete T-bread, which the given state of todo names on the line that creates it; todo creates the keys T-milk and T-bread and completes T-bread, so test reports nothing",
  [
    at("2026-10-25T10:00:00+09:00"),
    mock(boardScreen, [
      todo.tasks,
      {
        result: "fulfilled",
        output: {
          tasks: [
            { taskId: "T-milk", title: "Buy milk" },
            { taskId: "T-bread", title: "Buy bread" },
          ],
        },
      },
    ]),
    operate(boardScreen, "complete", { taskId: "T-bread" }),
    mock(boardScreen, [todo.completeTask, { result: "accepted" }]),
  ],
  { given: { todo: todo.states.namedMilkAndBread } },
);

export const showsOneWrongTitleOfThirty = scenario(
  "Answer thirty tasks with one title that todo does not have; the tasks are alike but for the keys that todo creates, so test reports unproducibleAnswer at once instead of trying each order of them",
  [
    at("2026-10-25T10:00:00+09:00"),
    mock(boardScreen, [
      todo.tasks,
      {
        result: "fulfilled",
        output: {
          tasks: Array.from({ length: 30 }, (_, i) => ({
            taskId: `T-${i + 1}`,
            title: i === 0 ? "Buy bread" : "Buy milk",
          })),
        },
      },
    ]),
  ],
  { given: { todo: todo.states.thirtyMilks } },
);

export const showsThirtyTasksWithOneKeyTwice = scenario(
  "Answer thirty tasks of one title, two of them with one key; every task of todo fits every task of the mock, and no order of them binds the keys one to one, so the search for one stops after its tries and test reports peerSearchLimit",
  [
    at("2026-10-25T10:00:00+09:00"),
    mock(boardScreen, [
      todo.tasks,
      {
        result: "fulfilled",
        output: {
          tasks: Array.from({ length: 30 }, (_, i) => ({ taskId: `T-${i === 29 ? 1 : i + 1}`, title: "Buy milk" })),
        },
      },
    ]),
  ],
  { given: { todo: todo.states.thirtyMilks } },
);

const watchingTasks = subscribe(todo.tasks, {});

export const endsTodoSubscriptionTwice = scenario(
  "Subscribe to the tasks of todo from elsewhere and end the subscription twice; todo's run reports unopenedSubscription at the second end, so test reports it at that line",
  [
    at("2026-10-25T10:00:00+09:00"),
    elsewhere(todo, watchingTasks),
    elsewhere(todo, unsubscribe(watchingTasks)),
    elsewhere(todo, unsubscribe(watchingTasks)),
  ],
);
