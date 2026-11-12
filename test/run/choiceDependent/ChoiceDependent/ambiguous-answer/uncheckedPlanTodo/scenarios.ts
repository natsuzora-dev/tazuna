import { at, mock, scenario, send } from "@natsuzora-dev/tazuna";
import { calendar } from "../calendar/contract.ts";
import { addTask, planner } from "./uncheckedPlanTodo.ts";

const day = { result: "fulfilled", output: { day: "2026-10-26T00:00:00+09:00" } } as const;

export const addOneWithUncheckedPlan = scenario(
  "Add a task; the first answer, which goes to the longest-waiting request, for the reminder day, can go to the plan day request, which has the same input, and then the holiday query changes, so test reports answerChoice",
  [
    at("2026-10-25T09:00:00+09:00"),
    send(addTask, { taskId: "task-1", title: "Buy milk" }),
    mock(planner, [calendar.nextDay, day]),
    mock(planner, [calendar.nextDay, day]),
  ],
);
