import { at, cannotOperate, mock, operate, scenario } from "@natsuzora-dev/tazuna";
import { todo } from "../todo/contract.ts";
import { editScreen } from "./editScreen.ts";
import { taskScreen } from "./taskScreen.ts";

const shown = (isCompleted: boolean) => mock(taskScreen, [todo.task, { result: "fulfilled", output: { isCompleted } }]);

export const offersDecide = scenario(
  "Operate complete before the task answer, while a completed task is shown, and while an open task is shown; the offers of complete return [] before the task answer arrives and while a completed task is shown, so taskScreen does not accept complete then. While an open task is shown, taskScreen accepts complete and sends completeTask",
  [
    at("2026-10-25T10:00:00+09:00"),
    cannotOperate(taskScreen, "complete"),
    shown(true),
    cannotOperate(taskScreen, "complete"),
    shown(false),
    operate(taskScreen, "complete"),
    mock(taskScreen, [todo.completeTask, { result: "accepted" }]),
  ],
);

export const innermostOffers = scenario(
  "Show an open task, complete it, and accept; after completeTask is accepted and taskScreen enters completed, the offers of completed apply instead of those of root, so taskScreen does not accept complete even though the task answer shows an open task",
  [
    at("2026-10-25T10:00:00+09:00"),
    shown(false),
    operate(taskScreen, "complete"),
    mock(taskScreen, [todo.completeTask, { result: "accepted" }]),
    cannotOperate(taskScreen, "complete"),
  ],
);

export const acceptedWithoutTransition = scenario(
  "Show an open task and operate complete twice; the offers of complete of root return [{}] while taskScreen waits for the answer to completeTask, so taskScreen accepts complete, but completing has no transition on complete, so it sends no second completeTask",
  [
    at("2026-10-25T10:00:00+09:00"),
    shown(false),
    operate(taskScreen, "complete"),
    operate(taskScreen, "complete"),
    mock(taskScreen, [todo.completeTask, { result: "accepted" }]),
  ],
);

export const unionOfRegionOffers = scenario(
  "Operate save on editScreen twice; while editScreen is in both renaming and completing, the offers of save of completing return [{}], so editScreen accepts save even though the offers of save of renaming return []",
  [at("2026-10-25T10:00:00+09:00"), operate(editScreen, "save"), operate(editScreen, "save")],
);

export const parentlessSideBySide = scenario(
  "Save on editScreen, show an open task, complete on taskScreen, and save again; taskScreen and editScreen have no parent, so both are topmost screens, and taskScreen accepts complete after the save of editScreen, and then editScreen accepts save",
  [
    at("2026-10-25T10:00:00+09:00"),
    operate(editScreen, "save"),
    shown(false),
    operate(taskScreen, "complete"),
    operate(editScreen, "save"),
  ],
);

export const datetimeOffers = scenario(
  "Operate remind on taskScreen; its offers return the at as a Temporal.Instant, and the list of accepted operations and the operation line of the trace hold that at as an ISO 8601 string",
  [at("2026-10-25T10:00:00+09:00"), operate(taskScreen, "remind", { at: "2026-10-25T03:00:00Z" })],
);
