import { external, fulfilled } from "@natsuzora-dev/tazuna";
import { calendar } from "../calendar/contract.ts";
import { addTask, scenario } from "./todo.ts";

const nextDay = fulfilled({ day: "2026-10-26T00:00:00+09:00" });

export const answerToReplacedCopy = scenario(
  "Add task-1 at 10:00 and answer twice at 11:00; the copy of task-1 enters asking and sends calendar.nextDay#1. The request is not stale yet when the answer arrives. perTask reenters rows through an always transition before it processes the answer, so the copy of task-1 ends, calendar.nextDay#1 becomes stale, and a new copy of the same key enters asking. The answer to the stale request does not reach the new copy, so the new copy stays in asking and sends calendar.nextDay#2, which the second answer line answers",
  {
    given: { start: "2026-10-25T10:00:00+09:00", records: { Task: [] }, peers: { calendar: external(calendar) } },
    when: (w) => {
      const adding = w.client.send(addTask, { taskId: "task-1" });
      const first = adding.request(calendar.nextDay);
      w.net.deliver(first);
      w.clock.at("2026-10-25T11:00:00+09:00");
      const answered = w.net.deliver(w.peer.calendar.answer(first, nextDay));
      const second = answered.request(calendar.nextDay);
      w.net.deliver(second);
      w.net.deliver(w.peer.calendar.answer(second, nextDay));
    },
    then: () => [],
  },
);
