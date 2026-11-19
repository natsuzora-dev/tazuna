import { run } from "@natsuzora-dev/tazuna";
import { todo } from "../todo/contract.ts";
import { scenario } from "./feed.ts";

export const start = scenario(
  "Start the service; recentScreen subscribes to recent with limit 0, which todo rejects with invalid-input as its input schema does not take it, so test reports inputSchema of feed, the sender",
  {
    given: {
      start: "2026-10-25T09:00:00+09:00",
      records: {},
      peers: [run(todo, { Task: [] })],
    },
    when: (w) => {
      const reached = w.net.deliver(w.startup.subscription(todo.recent));
      w.net.deliver(reached.answer(reached));
    },
    then: () => [],
  },
);
