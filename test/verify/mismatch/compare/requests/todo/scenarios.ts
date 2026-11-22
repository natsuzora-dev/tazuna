import { external, parseInstant } from "@natsuzora-dev/tazuna";
import { calendar } from "../calendar/contract.ts";
import { addTask, scenario } from "./todo.ts";

export const addHourly = scenario({
  description: "Add a task every hour; no violation",
  given: { start: parseInstant("2026-10-25T00:00:00Z"), records: { Task: [] }, peers: [external(calendar)] },
  when: (w) => {
    w.net.leaveInFlight(w.client.send(addTask, { taskId: "task-1", title: "Buy milk" }).request(calendar.nextDay));
    w.clock.at(parseInstant("2026-10-25T01:00:00Z"));
    w.net.leaveInFlight(w.client.send(addTask, { taskId: "task-2", title: "Buy eggs" }).request(calendar.nextDay));
    w.clock.at(parseInstant("2026-10-25T02:00:00Z"));
    w.net.leaveInFlight(w.client.send(addTask, { taskId: "task-3", title: "Buy tea" }).request(calendar.nextDay));
  },
  then: () => [],
});

export const addHourlyWrongRequests = scenario({
  description:
    "Same inputs as addHourly; the implementation trace of this scenario sends calendar.nextDay with another input, misses the second one, and sends an extra calendar.book, so verify reports Mismatch.request, missingLine, and unexpectedLine",
  given: { start: parseInstant("2026-10-25T00:00:00Z"), records: { Task: [] }, peers: [external(calendar)] },
  when: (w) => {
    w.net.leaveInFlight(w.client.send(addTask, { taskId: "task-1", title: "Buy milk" }).request(calendar.nextDay));
    w.clock.at(parseInstant("2026-10-25T01:00:00Z"));
    w.net.leaveInFlight(w.client.send(addTask, { taskId: "task-2", title: "Buy eggs" }).request(calendar.nextDay));
    w.clock.at(parseInstant("2026-10-25T02:00:00Z"));
    w.net.leaveInFlight(w.client.send(addTask, { taskId: "task-3", title: "Buy tea" }).request(calendar.nextDay));
  },
  then: () => [],
});
