import { homeScreen } from "./screens.ts";
import { addTask, archiveTask, dropTask, scenario } from "./todo.ts";

const given = { start: "2026-10-25T10:00:00+09:00", records: {}, peers: {} } as const;

export const onDoneAfterExit = scenario(
  "Add a task and archive it; on the taskFinished of archiveTask, tracker enters finished of tracking and queues the onDone of tracking. On the taskArchived of the same message, tracker exits tracking, so the onDone processed later is dropped and tracker sends no logTask",
  {
    given,
    when: (w) => {
      w.client.send(addTask, {});
      w.client.send(archiveTask, {});
    },
    then: () => [],
  },
);

export const eventAfterClose = scenario(
  "Open the pick screen and drop a task; homeScreen and pickScreen receive taskDropped, and homeScreen, which opened first, processes it first. homeScreen exits picking and closes pickScreen, so the taskDropped that arrives at pickScreen afterward is dropped",
  {
    given,
    when: (w) => {
      w.user.operate(w.begin.screen(homeScreen), "openPick");
      w.client.send(dropTask, {});
    },
    then: () => [],
  },
);
