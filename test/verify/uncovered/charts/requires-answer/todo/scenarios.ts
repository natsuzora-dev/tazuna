import { external, parseInstant } from "@natsuzora-dev/tazuna";
import { calendar } from "../calendar/calendar.ts";
import { addTask, scenario } from "./todo.ts";

export const asked = scenario({
  description:
    "Add a task, which leaves the question to calendar unanswered; no trace answers it, so verify --coverage reports planner's transitions on the answer and the states that they enter",
  given: { start: parseInstant("2026-10-25T00:00:00Z"), records: { Task: [] }, peers: [external(calendar)] },
  when: (w) => {
    const add = w.client.send(addTask, { taskId: "task-1" });
    w.net.leaveInFlight(add.request(calendar.nextDay));
  },
  then: () => [],
});
