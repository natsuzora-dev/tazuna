import { external, fulfilled } from "@natsuzora-dev/tazuna";
import { calendar } from "../calendar/contract.ts";
import { addTasks, scenario } from "./todo.ts";

const given = {
  start: "2026-10-25T10:00:00Z",
  records: { Task: [], Last: { taskId: "" } },
  peers: [external(calendar)],
} as const;

export const lastAnswer = scenario(
  "Add task-1 and task-2; the copy of each asks calendar, and one line delivers both answers, which answer different requests: todo records the task whose answer it processes last, which nothing outside tells, so test reports stepOrder at the two arrivals",
  {
    given,
    when: (w) => {
      const add = w.client.send(addTasks, { taskIds: ["task-1", "task-2"] });
      const asked = add.request(calendar.nextBusinessDay);
      w.net.deliver(asked);
      w.net.deliver(w.peer.calendar.answer(asked, fulfilled({ day: "2026-10-26T00:00:00Z" })));
    },
    then: () => [],
  },
);
