import { external } from "@natsuzora-dev/tazuna";
import { calendar } from "../calendar/contract.ts";
import { addTask, scenario } from "./todo.ts";

export const addOne = scenario(
  "Add a task; the snapshot's after names earlier lines of the same window; no violation",
  {
    given: { start: "2026-10-25T00:00:00Z", records: { Task: [] }, peers: [external(calendar)] },
    when: (w) => {
      w.net.leaveInFlight(w.client.send(addTask, { taskId: "task-1", title: "Buy milk" }).request(calendar.nextDay));
    },
    then: () => [],
  },
);

export const addOneUnknownAfter = scenario(
  "Add a task; in the snapshot, taskAdded's after names the later taskCountChanged#1 and taskCountChanged's after names taskAdded#9, which no line has, so verify reports unknownAfter",
  {
    given: { start: "2026-10-25T00:00:00Z", records: { Task: [] }, peers: [external(calendar)] },
    when: (w) => {
      w.net.leaveInFlight(w.client.send(addTask, { taskId: "task-1", title: "Buy milk" }).request(calendar.nextDay));
    },
    then: () => [],
  },
);
