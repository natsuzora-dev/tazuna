import { external } from "@natsuzora-dev/tazuna";
import { todo } from "../todo/contract.ts";
import { scenario } from "./data.ts";

export const answerToClosedScreen = scenario(
  "Answer the subscription at 11:00; listScreen opens at 10:00 and subscribes to todo.tasks. The subscription has not ended yet when the answer arrives. listScreen enters closed through an always transition and closes before it processes the answer, so the subscription ends and the answer does not reach listScreen. The answer is a rejection that blames the caller, but it reaches no closed screen, so no rejection is reported",
  {
    given: { start: "2026-10-25T10:00:00+09:00", records: {}, peers: { todo: external(todo) } },
    when: (w) => {
      w.clock.at("2026-10-25T11:00:00+09:00");
      const tasks = w.begin.request(todo.tasks);
      w.peer.todo.answer(tasks, {
        result: "rejected",
        rejection: { kind: "requires", reason: "isListed" },
      });
      // The end of the subscription that closing listScreen sent.
      w.net.inFlight(tasks);
    },
    then: () => [],
  },
);
