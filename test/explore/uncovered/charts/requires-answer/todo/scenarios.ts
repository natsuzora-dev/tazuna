import { external, parseInstant } from "@natsuzora-dev/tazuna";
import { calendar } from "../calendar/calendar.ts";
import { addTask, scenario } from "./todo.ts";

export const asked = scenario({
  description:
    "Add a task, which leaves the question to calendar unanswered; test answers it, and its requires rejection names isWeekday, so planner enters refused",
  given: { start: parseInstant("2026-10-25T00:00:00Z"), records: { Task: [] }, peers: [external(calendar)] },
  when: (w) => {
    const add = w.client.send(addTask, { taskId: "task-1" });
    w.net.leaveInFlight(add.request(calendar.nextDay));
  },
  then: () => [],
});
