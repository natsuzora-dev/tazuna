import { at, mock, operate, scenario } from "@natsuzora-dev/tazuna";
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
