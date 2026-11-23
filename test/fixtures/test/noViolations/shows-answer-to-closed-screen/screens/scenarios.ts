import { external, parseInstant, rejected } from "@natsuzora-dev/tazuna";
import { todo } from "../todo/contract.ts";
import { scenario } from "./data.ts";

export const answerToClosedScreen = scenario({
  description:
    "Answer the subscription at 11:00; listScreen opens at 10:00 and subscribes to todo.tasks. The subscription has not ended yet when the answer arrives. listScreen enters closed through an always transition and closes before it processes the answer, so the subscription ends and the answer does not reach listScreen. The answer is a rejection that blames the caller, but it reaches no closed screen, so no rejection is reported",
  given: { start: parseInstant("2026-10-25T10:00:00+09:00"), records: {}, peers: [external(todo)] },
  when: (w) => {
    const tasks = w.startup.subscription(todo.tasks);
    w.net.deliver(tasks);
    w.clock.at(parseInstant("2026-10-25T11:00:00+09:00"));
    const answered = w.net.deliver(w.peer.todo.answer(tasks, rejected("requires", "isListed")));
    w.net.leaveInFlight(answered.end(tasks));
  },
  then: () => [],
});
