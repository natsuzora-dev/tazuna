import { parseInstant } from "@natsuzora-dev/tazuna";
import { scenario } from "./todo.ts";

export const givenUnassigned = scenario({
  description:
    "Given an unassigned task at 09:00, let the clock reach 11:00; test reports missedResponse assigned, due at 10:00, since Given records are observed when the service begins",
  given: {
    start: parseInstant("2026-10-25T09:00:00+09:00"),
    records: { Task: [{ id: "task-0", assignee: null }] },
    peers: [],
  },
  when: (w) => {
    w.clock.at(parseInstant("2026-10-25T11:00:00+09:00"));
  },
  then: () => [],
});
