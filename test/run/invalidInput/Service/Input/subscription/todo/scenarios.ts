import { scenario, taskTitles } from "./todo.ts";

export const endUnopened = scenario(
  "Subscribe, unsubscribe from the open subscription, then subscribe again; no violation",
  {
    given: { start: "2026-10-25T09:00:00+09:00", records: { Task: [] }, peers: {} },
    when: (w) => {
      const titles = w.client.subscribe(taskTitles, {});
      w.client.unsubscribe(titles);
      w.client.subscribe(taskTitles, {});
    },
    then: () => [],
  },
);

export const endUnopenedAndSubscribeTwice = scenario(
  "Unsubscribe from a subscription twice, then subscribe and send that subscribe again with its id; the second unsubscribe ends no open subscription and the resent subscribe reuses the id of the open one, so test reports unopenedSubscription and reusedSubscriptionId",
  {
    given: { start: "2026-10-25T09:00:00+09:00", records: { Task: [] }, peers: {} },
    when: (w) => {
      const titles = w.client.subscribe(taskTitles, {});
      w.client.unsubscribe(titles);
      w.client.unsubscribe(titles);
      w.client.resend(w.client.subscribe(taskTitles, {}));
    },
    then: () => [],
  },
);
