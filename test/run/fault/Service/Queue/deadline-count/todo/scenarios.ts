import { scenario } from "./todo.ts";

export const weekLater = scenario(
  "Start the service and come back a week later; more than 10000 minutes have passed, so test reports exceededDueDeadlines",
  {
    given: { start: "2026-10-25T09:00:00+09:00", records: {}, peers: {} },
    when: (w) => {
      w.clock.at("2026-11-01T09:00:00+09:00");
    },
    then: () => [],
  },
);
