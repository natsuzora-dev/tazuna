import { external } from "@natsuzora-dev/tazuna";
import { calendar } from "../calendar/contract.ts";
import { addTasks, scenario } from "./todo.ts";

const given = {
  start: "2026-10-25T10:00:00Z",
  records: { Task: [] },
  peers: { calendar: external(calendar) },
} as const;

export const sameAnswers = scenario(
  "Add task-1 and task-2; the copy of each asks calendar with the same input, so one handle names both requests, the lines deliver and answer each, and calendar answers both with Monday: in either order both tasks are due Monday",
  {
    given,
    when: (w) => {
      const add = w.client.send(addTasks, { taskIds: ["task-1", "task-2"] });
      const asked = add.request(calendar.nextBusinessDay);
      w.net.deliver(asked);
      w.net.deliver(w.peer.calendar.answer(asked, { result: "fulfilled", output: { day: "2026-10-26T00:00:00Z" } }));
    },
    then: () => [],
  },
);
