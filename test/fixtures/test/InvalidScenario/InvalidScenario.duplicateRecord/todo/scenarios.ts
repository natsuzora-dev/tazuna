import { parseInstant } from "@natsuzora-dev/tazuna";
import { scenario } from "./todo.ts";

export const twoMilks = scenario({
  description: "Given writes two tasks with the key task-1",
  given: {
    start: parseInstant("2026-10-25T09:00:00+09:00"),
    records: {
      Task: [
        { id: "task-1", title: "Buy milk" },
        { id: "task-1", title: "Buy eggs" },
      ],
    },
    peers: [],
  },
  when: () => {},
  then: () => [],
});
