import { external, fulfilled } from "@natsuzora-dev/tazuna";
import { calendar } from "../calendar/contract.ts";
import { addTask, scenario } from "./todo.ts";

export const answerAfterAlways = scenario({
  description:
    "Add a task at 10:00 and answer at 12:00; planner enters asking and sends calendar.nextDay. The request is not stale yet when the answer arrives. planner evaluates its always guards before it processes the answer and enters gaveUp, so the answer takes no onFulfilled transition and planner sends no noteAnswer",
  given: { start: "2026-10-25T10:00:00+09:00", records: {}, peers: [external(calendar)] },
  when: (w) => {
    const adding = w.client.send(addTask, { taskId: "task-1" });
    const nextDay = adding.request(calendar.nextDay);
    w.net.deliver(nextDay);
    w.clock.at("2026-10-25T12:00:00+09:00");
    w.net.deliver(w.peer.calendar.answer(nextDay, fulfilled({ day: "2026-10-26T00:00:00+09:00" })));
  },
  then: () => [],
});
