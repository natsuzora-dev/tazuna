import { external } from "@natsuzora-dev/tazuna";
import { calendar } from "../calendar/contract.ts";
import { addTasks, scenario } from "./todo.ts";

const given = {
  start: "2026-10-25T10:00:00Z",
  records: { Task: [] },
  peers: { calendar: external(calendar) },
} as const;
const monday = { result: "fulfilled", output: { day: "2026-10-26T00:00:00Z" } } as const;
const tuesday = { result: "fulfilled", output: { day: "2026-10-27T00:00:00Z" } } as const;

export const sameAnswers = scenario(
  "Add task-1 and task-2; the copy of each asks calendar with the same input, and calendar answers both with Monday, so whichever request each handle names, both tasks are due Monday",
  {
    given,
    when: (w) => {
      const add = w.client.send(addTasks, { taskIds: ["task-1", "task-2"] });
      const [first, second] = add.requests(calendar.nextBusinessDay);
      w.net.deliver(first);
      w.net.deliver(second);
      w.net.deliver(w.peer.calendar.answer(first, monday));
      w.net.deliver(w.peer.calendar.answer(second, monday));
    },
    then: () => [],
  },
);

export const differentAnswers = scenario(
  "Add task-1 and task-2; calendar answers the first handle with Monday and the second with Tuesday, but nothing outside tells which request is task-1's, so the task due Monday depends on which request each handle names: ChoiceDependent.assignment",
  {
    given,
    when: (w) => {
      const add = w.client.send(addTasks, { taskIds: ["task-1", "task-2"] });
      const [first, second] = add.requests(calendar.nextBusinessDay);
      w.net.deliver(first);
      w.net.deliver(second);
      w.net.deliver(w.peer.calendar.answer(first, monday));
      w.net.deliver(w.peer.calendar.answer(second, tuesday));
    },
    then: () => [],
  },
);

export const oneLeft = scenario(
  "Add task-1 and task-2 and name only the first request, which calendar leaves unanswered; the second request has no line, so it is reported as left in flight",
  {
    given,
    when: (w) => {
      const add = w.client.send(addTasks, { taskIds: ["task-1", "task-2"] });
      const [first] = add.requests(calendar.nextBusinessDay);
      w.net.deliver(first);
      w.peer.calendar.leaveUnanswered(first);
    },
    then: () => [],
  },
);

export const handleBeyond = scenario(
  "Add task-1 and task-2 and name a third request, which the copies never sent: unresolvedReference",
  {
    given,
    when: (w) => {
      const add = w.client.send(addTasks, { taskIds: ["task-1", "task-2"] });
      const [first, second, third] = add.requests(calendar.nextBusinessDay);
      w.net.deliver(first);
      w.net.deliver(second);
      w.net.deliver(third);
    },
    then: () => [],
  },
);
