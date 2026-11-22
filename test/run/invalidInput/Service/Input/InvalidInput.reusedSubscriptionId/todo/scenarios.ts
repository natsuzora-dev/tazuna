import { parseInstant } from "@natsuzora-dev/tazuna";
import { scenario, taskTitles } from "./todo.ts";

export const subscribeTwice = scenario({
  description:
    "Subscribe, and send that subscribe again with its id while it is open; the resent subscribe reuses the id of the open one",
  given: { start: parseInstant("2026-10-25T09:00:00+09:00"), records: { Task: [] }, peers: [] },
  when: (w) => {
    w.client.resend(w.client.subscribe(taskTitles, {}));
  },
  then: () => [],
});
