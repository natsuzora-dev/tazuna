import { parseInstant } from "@natsuzora-dev/tazuna";
import { scenario } from "./todo.ts";

export const start = scenario({
  description:
    "Start the service with two tasks of 5e15 points; the initial edge of running fills the total of watching, whose sum is no safe integer, so the sum faults and test reports exception of watcher",
  given: {
    start: parseInstant("2026-10-25T09:00:00+09:00"),
    records: {
      Task: [
        { id: "task-1", points: 5_000_000_000_000_000 },
        { id: "task-2", points: 5_000_000_000_000_000 },
      ],
    },
    peers: [],
  },
  when: (_w) => {},
  then: () => [],
});
