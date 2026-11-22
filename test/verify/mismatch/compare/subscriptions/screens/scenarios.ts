import { parseInstant, skip } from "@natsuzora-dev/tazuna";
import { todo } from "../todo/contract.ts";
import { given, scenario, taskListScreen } from "./screens.ts";

const arranged = given({
  start: parseInstant("2026-10-25T00:00:00Z"),
  records: {},
  peers: [skip(todo, "verify compares the subscriptions that the screen opens, not their answers")],
});

export const filterAndClose = scenario({
  description: "Filter the list and close it; no violation",
  given: arranged,
  when: (w) => {
    const list = w.startup.screen(taskListScreen);
    w.user.operate(list, "filter", { prefix: "Buy" });
    w.user.operate(list, "close");
  },
  then: () => [],
});

export const filterAndCloseWrongSubscriptions = scenario({
  description:
    "Same inputs as filterAndClose; the implementation trace of this scenario opens the first subscription with another input and never ends it, and opens an extra subscription at the end, so verify reports Mismatch.request, missingLine, and unexpectedSubscription",
  given: arranged,
  when: (w) => {
    const list = w.startup.screen(taskListScreen);
    w.user.operate(list, "filter", { prefix: "Buy" });
    w.user.operate(list, "close");
  },
  then: () => [],
});
