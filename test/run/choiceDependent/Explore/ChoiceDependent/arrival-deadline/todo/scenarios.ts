import { external, fulfilled } from "@natsuzora-dev/tazuna";
import { calendar } from "../calendar/contract.ts";
import { addTasks, given, scenario } from "./todo.ts";

const arranged = given({
  start: "2026-10-25T10:00:00Z",
  records: { Task: [], Last: { taskId: "" } },
  peers: [external(calendar)],
});

export const lastAnswerFiled = scenario(
  "As arrival-order's lastAnswer, but each copy stays and its done state has an overdue deadline, which fires at the end of each arrival as a message of its own: the arrival step still names its own message, so test reports stepOrder at the two arrivals",
  {
    given: arranged,
    when: (w) => {
      const add = w.client.send(addTasks, { taskIds: ["task-1", "task-2"] });
      const asked = add.request(calendar.nextBusinessDay);
      w.net.deliver(asked);
      w.net.deliver(w.peer.calendar.answer(asked, fulfilled({ day: "2026-10-26T00:00:00Z" })));
    },
    then: () => [],
  },
);
