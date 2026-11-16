import { at, scenario, subscribe, unsubscribe } from "@natsuzora-dev/tazuna";
import { taskTitles } from "./todo.ts";

const titles = subscribe(taskTitles, {});

export const endUnopened = scenario(
  "Subscribe, unsubscribe from the open subscription, then subscribe again; no violation",
  [at("2026-10-25T09:00:00+09:00"), titles, unsubscribe(titles), subscribe(taskTitles, {})],
);

export const endUnopenedAndSubscribeTwice = scenario(
  "Unsubscribe from a subscription twice, then subscribe twice with the id s2; the second unsubscribe ends no open subscription and the second subscribe reuses s2, so test reports unopenedSubscription and reusedSubscriptionId",
  [
    at("2026-10-25T09:00:00+09:00"),
    titles,
    unsubscribe(titles),
    unsubscribe(titles),
    subscribe(taskTitles, {}, { id: "s2" }),
    subscribe(taskTitles, {}, { id: "s2" }),
  ],
);
