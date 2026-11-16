import { external } from "@natsuzora-dev/tazuna";
import { calendar } from "../calendar/contract.ts";
import { addTask, completeTask, reopenTask, scenario } from "./todo.ts";

export const copiesFollowItems = scenario(
  "Add task-1 and task-2, complete task-1, and reopen it; dayNoter runs a copy for each added task and asks calendar for the next day in each copy. Completing task-1 removes it from items, so its copy exits its states and the answer to its request is stale. Reopening task-1 makes dayNoter run a new copy of task-1, which asks calendar again",
  {
    given: { start: "2026-10-25T10:00:00Z", records: { Task: [] }, peers: { calendar: external(calendar) } },
    when: (w) => {
      const first = w.client.send(addTask, { taskId: "task-1" });
      w.clock.at("2026-10-25T10:05:00Z");
      const second = w.client.send(addTask, { taskId: "task-2" });
      w.client.send(completeTask, { taskId: "task-1" });
      w.peer.calendar.answer(first.request(calendar.nextDay), {
        result: "fulfilled",
        output: { day: "2026-10-26T00:00:00Z" },
      });
      const reopening = w.client.send(reopenTask, { taskId: "task-1" });
      w.peer.calendar.answer(second.request(calendar.nextDay), {
        result: "fulfilled",
        output: { day: "2026-10-27T00:00:00Z" },
      });
      w.peer.calendar.answer(reopening.request(calendar.nextDay), {
        result: "fulfilled",
        output: { day: "2026-10-28T00:00:00Z" },
      });
    },
    then: () => [],
  },
);
