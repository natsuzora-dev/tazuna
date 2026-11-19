import { external, fulfilled } from "@natsuzora-dev/tazuna";
import { calendar } from "../calendar/contract.ts";
import { addTask, scenario } from "./todo.ts";

const given = {
  start: "2026-10-25T00:00:00Z",
  records: { Task: [] },
  peers: [external(calendar)],
} as const;

export const twoDays = scenario(
  "Add a task and answer the calendar.nextDay request; its snapshot, edited by hand, has the planner send two equal calendar.nextDay requests and answers them with different days. The trace's two requests are equal too, so no line tells which of them stands for the first, and the request that the harness gave the first answer to decides what the implementation got; verify reports Uncomparable.ambiguous",
  {
    given,
    when: (w) => {
      const ask = w.client.send(addTask, { taskId: "task-1", title: "Buy milk" }).request(calendar.nextDay);
      w.net.deliver(ask);
      w.net.deliver(w.peer.calendar.answer(ask, fulfilled({ day: "2026-10-26T00:00:00Z" })));
    },
    then: () => [],
  },
);

export const twoDaysAlike = scenario(
  "Same inputs as twoDays; its snapshot, edited by hand, answers the two equal requests with the same day, so whichever request the harness gives each answer to, the implementation gets the same inputs; no violation",
  {
    given,
    when: (w) => {
      const ask = w.client.send(addTask, { taskId: "task-1", title: "Buy milk" }).request(calendar.nextDay);
      w.net.deliver(ask);
      w.net.deliver(w.peer.calendar.answer(ask, fulfilled({ day: "2026-10-26T00:00:00Z" })));
    },
    then: () => [],
  },
);
