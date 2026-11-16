import { external } from "@natsuzora-dev/tazuna";
import { calendar } from "../calendar/contract.ts";
import { addTask, scenario } from "./todo.ts";

export const addOne = scenario(
  "Add a task; the implementation trace keeps the snapshot's order and times; no violation",
  {
    given: { start: "2026-10-25T00:00:00Z", records: { Task: [] }, peers: { calendar: external(calendar) } },
    when: (w) => {
      const add = w.client.send(addTask, { taskId: "task-1", title: "Buy milk" });
      w.net.inFlight(add.request(calendar.nextDay));
    },
    then: () => [],
  },
);

export const addOneReordered = scenario(
  "Add a task; the implementation trace sends taskCountChanged before taskAdded and the query 5 seconds late, so verify reports lineOrder and Mismatch.time",
  {
    given: { start: "2026-10-25T00:00:00Z", records: { Task: [] }, peers: { calendar: external(calendar) } },
    when: (w) => {
      const add = w.client.send(addTask, { taskId: "task-1", title: "Buy milk" });
      w.net.inFlight(add.request(calendar.nextDay));
    },
    then: () => [],
  },
);
