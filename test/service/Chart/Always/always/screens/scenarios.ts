import { at, mock, operate, scenario } from "@natsuzora-dev/tazuna";
import { todo } from "../todo/contract.ts";
import { listScreen } from "./listScreen.ts";

export const settlesAfterShownChange = scenario(
  "Operate leave on listScreen; listScreen enters leaving, and at the end of the macrostep ends its subscription to tasks and sets shown.tasks to null. listScreen evaluates its always guards after the change of shown and enters cleared in the same message, so it is not in leaving when the message is processed",
  [
    at("2026-10-25T10:00:00+09:00"),
    mock(listScreen, [todo.tasks, { result: "fulfilled", output: { taskIds: [] } }]),
    operate(listScreen, "leave"),
  ],
);
