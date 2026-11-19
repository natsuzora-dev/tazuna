import { external } from "@natsuzora-dev/tazuna";
import { calendar } from "../calendar/contract.ts";
import { addTask, scenario } from "./todo.ts";

export const addHourlyWrongRequests = scenario({
  description: "Add a task each hour; the implementation trace sends no nextDay query for the second task",
  given: { start: "2026-10-25T00:00:00Z", records: { Task: [] }, peers: [external(calendar)] },
  when: (w) => {
    w.net.leaveInFlight(w.client.send(addTask, { taskId: "task-1", title: "Buy milk" }).request(calendar.nextDay));
    w.clock.at("2026-10-25T01:00:00Z");
    w.net.leaveInFlight(w.client.send(addTask, { taskId: "task-2", title: "Buy eggs" }).request(calendar.nextDay));
    w.clock.at("2026-10-25T02:00:00Z");
    w.net.leaveInFlight(w.client.send(addTask, { taskId: "task-3", title: "Buy tea" }).request(calendar.nextDay));
  },
  then: () => [],
});
