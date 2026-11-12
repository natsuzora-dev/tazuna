import { at, cannotOperate, operate, scenario } from "@natsuzora-dev/tazuna";
import { confirmDialog, listScreen } from "./screens.ts";

export const pickAndCancel = scenario("Pick a shown task, open the dialog, and cancel it; no violation", [
  at("2026-10-25T09:00:00+09:00"),
  operate(listScreen, "pick", { taskId: "task-1" }),
  operate(listScreen, "clear"),
  operate(confirmDialog, "cancel"),
  operate(listScreen, "pick", { taskId: "task-2" }),
]);

export const cannotPickUnaccepted = scenario(
  "Assert that the dialog accepts no cancel before it opens, and the list no task that it does not show and no task while the dialog covers it; no violation",
  [
    at("2026-10-25T09:00:00+09:00"),
    cannotOperate(confirmDialog, "cancel"),
    cannotOperate(listScreen, "pick", { taskId: "task-3" }),
    operate(listScreen, "clear"),
    cannotOperate(listScreen, "pick", { taskId: "task-1" }),
  ],
);

export const cancelUnopened = scenario("Cancel the dialog before it opens; test reports screenNotOpen", [
  at("2026-10-25T09:00:00+09:00"),
  operate(confirmDialog, "cancel"),
]);

export const pickUnderDialog = scenario("Pick a task while the dialog covers the list; test reports coveredByModal", [
  at("2026-10-25T09:00:00+09:00"),
  operate(listScreen, "clear"),
  operate(listScreen, "pick", { taskId: "task-1" }),
]);

export const pickUnoffered = scenario("Pick a task that the list does not show; test reports payloadNotOffered", [
  at("2026-10-25T09:00:00+09:00"),
  operate(listScreen, "pick", { taskId: "task-3" }),
]);

export const cannotPickShown = scenario(
  "Assert that the list does not accept a task that it shows; test reports unexpectedlyAccepted",
  [at("2026-10-25T09:00:00+09:00"), cannotOperate(listScreen, "pick", { taskId: "task-1" })],
);

export const cannotClear = scenario(
  "Assert that the list does not accept clear, which has no offers; test reports unexpectedlyAccepted",
  [at("2026-10-25T09:00:00+09:00"), cannotOperate(listScreen, "clear")],
);
