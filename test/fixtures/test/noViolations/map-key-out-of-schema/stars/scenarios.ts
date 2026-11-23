import { parseInstant } from "@natsuzora-dev/tazuna";
import { scenario, starTask } from "./stars.ts";

export const keyOutOfSchema = scenario({
  description:
    "Star the task other-1; taskStarred, whose payload taskId does not fit the key schema, reaches no copy, and no copy marks",
  given: { start: parseInstant("2026-10-25T10:00:00+09:00"), records: {}, peers: [] },
  when: (w) => {
    w.client.as("client").send(starTask, { taskId: "other-1" });
  },
  then: () => [],
});
