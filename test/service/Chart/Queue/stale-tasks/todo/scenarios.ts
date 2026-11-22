import { parseInstant } from "@natsuzora-dev/tazuna";
import { addTask, archiveTask, given, scenario } from "./todo.ts";

const arranged = given({ start: parseInstant("2026-10-25T10:00:00+09:00"), records: {}, peers: [] });

export const onDoneAfterExit = scenario({
  description:
    "Add a task and archive it; on the taskFinished of archiveTask, tracker enters finished of tracking and queues the onDone of tracking. On the taskArchived of the same message, tracker exits tracking, so the onDone processed later is dropped and tracker sends no logTask",
  given: arranged,
  when: (w) => {
    w.client.send(addTask, {});
    w.client.send(archiveTask, {});
  },
  then: () => [],
});
