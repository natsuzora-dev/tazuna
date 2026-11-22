import { parseInstant, run } from "@natsuzora-dev/tazuna";
import { calendar } from "../calendar/contract.ts";
import { addTasks, given, scenario } from "./todo.ts";

const arranged = given({
  start: parseInstant("2026-10-25T10:00:00Z"),
  records: { Task: [] },
  peers: [run(calendar, { Booking: [] })],
});

export const sameDay = scenario({
  description:
    "Add task-1, task-2 and task-3 for Monday; the copy of each sends calendar the same reserve, so one handle names all three, and calendar books Monday for whichever it processes first and refuses the others: it processes equal requests differently, so which task is booked depends on which arrives first, which nothing outside tells, and test runs other arrival orders and reports ChoiceDependent.stepOrder at reserve once, naming the first two messages whose order changes the outcome",
  given: arranged,
  when: (w) => {
    const add = w.client.send(addTasks, {
      tasks: [
        { id: "task-1", day: "Mon" },
        { id: "task-2", day: "Mon" },
        { id: "task-3", day: "Mon" },
      ],
    });
    const reserving = w.net.deliver(add.request(calendar.reserve));
    w.net.deliver(reserving.answer(reserving));
  },
  then: () => [],
});

export const otherDays = scenario({
  description:
    "Add task-1 for Monday and task-2 for Tuesday; a pick names each reserve by its day, and calendar books both: no violation",
  given: arranged,
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
});
