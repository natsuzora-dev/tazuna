import { external, fulfilled, parseInstant } from "@natsuzora-dev/tazuna";
import { calendar } from "../calendar/contract.ts";
import { addTask, given, scenario } from "./todo.ts";

const arranged = given({
  start: parseInstant("2026-10-25T00:00:00Z"),
  records: { Task: [] },
  peers: [external(calendar)],
});

export const twoDays = scenario({
  description:
    "Add a task; planner and reminder send two equal calendar.nextDay requests. The trace answers them with different days, and its two requests are equal too, so no line tells which of them stands for which of the spec's, and which spec request the replay gives the first answer to decides what the spec got; verify reports Uncomparable.ambiguous",
  given: arranged,
  when: (w) => {
    const ask = w.client.send(addTask, { taskId: "task-1", title: "Buy milk" }).request(calendar.nextDay);
    w.net.deliver(ask);
    w.net.deliver(w.peer.calendar.answer(ask, fulfilled({ day: parseInstant("2026-10-26T00:00:00Z") })));
  },
  then: () => [],
});

export const twoDaysAlike = scenario({
  description:
    "Same inputs as twoDays; the trace answers the two equal requests with the same day, so whichever spec request the replay gives each answer to, the spec gets the same inputs; no violation",
  given: arranged,
  when: (w) => {
    const ask = w.client.send(addTask, { taskId: "task-1", title: "Buy milk" }).request(calendar.nextDay);
    w.net.deliver(ask);
    w.net.deliver(w.peer.calendar.answer(ask, fulfilled({ day: parseInstant("2026-10-26T00:00:00Z") })));
  },
  then: () => [],
});
