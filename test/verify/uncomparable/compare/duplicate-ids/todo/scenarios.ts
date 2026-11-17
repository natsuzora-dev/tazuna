import { external } from "@natsuzora-dev/tazuna";
import { calendar } from "../calendar/contract.ts";
import { addTask, scenario } from "./todo.ts";

const given = {
  start: "2026-10-25T00:00:00Z",
  records: { Task: [] },
  peers: { calendar: external(calendar) },
} as const;

export const addTwoReusedId = scenario(
  "Add two tasks an hour apart, and get the next day for the first; the implementation trace of this scenario gives the second calendar.nextDay request the id of the first, so the trace has two request lines with one id and verify reports Uncomparable.duplicateId",
  {
    given,
    when: (w) => {
      const first = w.client.send(addTask, { taskId: "task-1", title: "Buy milk" }).request(calendar.nextDay);
      w.net.deliver(first);
      w.net.deliver(w.peer.calendar.answer(first, { result: "fulfilled", output: { day: "2026-10-26T00:00:00Z" } }));
      w.clock.at("2026-10-25T01:00:00Z");
      w.net.leaveInFlight(w.client.send(addTask, { taskId: "task-2", title: "Buy eggs" }).request(calendar.nextDay));
    },
    then: () => [],
  },
);
