import { at, scenario, send } from "@natsuzora-dev/tazuna";
import { addTask, archiveTitle } from "./todo.ts";

export const archiveShared = scenario(
  "Archive a title that two tasks share; decide archives the title once per task in one Bag, so test reports sameRecordInBag",
  [
    at("2026-10-25T09:00:00+09:00"),
    send(addTask, { taskId: "task-1", title: "Buy milk" }),
    send(addTask, { taskId: "task-2", title: "Buy milk" }),
    send(archiveTitle, { title: "Buy milk" }),
  ],
);
