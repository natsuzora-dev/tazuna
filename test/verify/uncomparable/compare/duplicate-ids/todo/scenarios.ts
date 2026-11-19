import { external, fulfilled } from "@natsuzora-dev/tazuna";
import { calendar } from "../calendar/contract.ts";
import { addTask, given, scenario } from "./todo.ts";

const arranged = given({
  start: "2026-10-25T00:00:00Z",
  records: { Task: [] },
  peers: [external(calendar)],
});

export const addTwoReusedId = scenario({
  description:
    "Add two tasks an hour apart, and get the next day for the first; the implementation trace of this scenario gives the second calendar.nextDay request the id of the first, so the trace has two request lines with one id and verify reports Uncomparable.duplicateId",
  given: arranged,
  when: (w) => {
    const first = w.client.send(addTask, { taskId: "task-1", title: "Buy milk" }).request(calendar.nextDay);
    w.net.deliver(first);
    w.net.deliver(w.peer.calendar.answer(first, fulfilled({ day: "2026-10-26T00:00:00Z" })));
    w.clock.at("2026-10-25T01:00:00Z");
    w.net.leaveInFlight(w.client.send(addTask, { taskId: "task-2", title: "Buy eggs" }).request(calendar.nextDay));
  },
  then: () => [],
});
