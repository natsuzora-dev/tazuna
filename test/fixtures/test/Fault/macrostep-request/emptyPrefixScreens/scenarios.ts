import { parseInstant, rejected, run } from "@natsuzora-dev/tazuna";
import { todo } from "../todo/contract.ts";
import { scenario } from "./screens.ts";

export const show = scenario({
  description:
    "todo rejects the shown query with requires; titledScreen shows titled with an empty prefix, and a rejection other than unavailable fails it, so test reports rejectedShows",
  given: { start: parseInstant("2026-10-25T09:00:00+09:00"), records: {}, peers: [run(todo, { Task: [] })] },
  when: (w) => {
    const titled = w.startup.subscription(todo.titled);
    w.net.deliver(titled);
    w.net.deliver(w.peer.todo.answer(titled, rejected("requires", "notEmpty")));
  },
  then: () => [],
});
