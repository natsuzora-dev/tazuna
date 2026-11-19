import { run } from "@natsuzora-dev/tazuna";
import { todo } from "../todo/contract.ts";
import { scenario } from "./screens.ts";

export const show = scenario({
  description:
    "The network fails the subscription of the shown query, so titledScreen gets unavailable, which does not fail shows; no violation",
  given: { start: "2026-10-25T09:00:00+09:00", records: {}, peers: [run(todo, { Task: [] })] },
  when: (w) => {
    w.net.refuse(w.startup.subscription(todo.titled));
  },
  then: () => [],
});
