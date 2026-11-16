import { at, operate, scenario, send } from "@natsuzora-dev/tazuna";
import { homeScreen } from "./screens.ts";
import { addTask, archiveTask, dropTask } from "./todo.ts";

export const onDoneAfterExit = scenario(
  "Add a task and archive it; on the taskFinished of archiveTask, tracker enters finished of tracking and queues the onDone of tracking. On the taskArchived of the same message, tracker exits tracking, so the onDone processed later is dropped and tracker sends no logTask",
  [at("2026-10-25T10:00:00+09:00"), send(addTask, {}), send(archiveTask, {})],
);

export const eventAfterClose = scenario(
  "Open the pick screen and drop a task; homeScreen and pickScreen receive taskDropped, and homeScreen, which opened first, processes it first. homeScreen exits picking and closes pickScreen, so the taskDropped that arrives at pickScreen afterward is dropped",
  [at("2026-10-25T10:00:00+09:00"), operate(homeScreen, "openPick"), send(dropTask, {})],
);
