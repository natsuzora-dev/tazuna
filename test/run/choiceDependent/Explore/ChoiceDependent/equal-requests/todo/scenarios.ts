import { run } from "@natsuzora-dev/tazuna";
import { calendar } from "../calendar/contract.ts";
import { addTasks, scenario } from "./todo.ts";

const given = {
  start: "2026-10-25T10:00:00Z",
  records: { Task: [] },
  peers: { calendar: run(calendar, { Booking: [] }) },
} as const;

export const sameDay = scenario(
  "Add task-1 and task-2 for Monday; the copy of each sends calendar the same reserve, so one handle names both, and calendar books Monday for whichever it processes first and refuses the other: which task is booked depends on that order, which nothing outside tells, so test reports ChoiceDependent.deliveryOrder at reserve",
  {
    given,
    when: (w) => {
      const add = w.client.send(addTasks, {
        tasks: [
          { id: "task-1", day: "Mon" },
          { id: "task-2", day: "Mon" },
        ],
      });
      const reserving = w.net.deliver(add.request(calendar.reserve));
      w.net.deliver(reserving.answer(reserving));
    },
    then: () => [],
  },
);

export const otherDays = scenario(
  "Add task-1 for Monday and task-2 for Tuesday; a pick names each reserve by its day, and calendar books both: no violation",
  {
    given,
    when: (w) => {
      const add = w.client.send(addTasks, {
        tasks: [
          { id: "task-1", day: "Mon" },
          { id: "task-2", day: "Tue" },
        ],
      });
      const monday = w.net.deliver(add.request(calendar.reserve, { day: "Mon" }));
      const tuesday = w.net.deliver(add.request(calendar.reserve, { day: "Tue" }));
      w.net.deliver(monday.answer(monday));
      w.net.deliver(tuesday.answer(tuesday));
    },
    then: () => [],
  },
);
