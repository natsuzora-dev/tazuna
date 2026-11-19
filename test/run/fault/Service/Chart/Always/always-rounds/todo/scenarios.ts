import { scenario } from "./todo.ts";

export const start = scenario(
  "Start the service; flow alternates between a and b through always transitions without end, so test reports exceededAlwaysRounds",
  {
    given: { start: "2026-10-25T09:00:00+09:00", records: { Task: [] }, peers: [] },
    when: (_w) => {},
    then: () => [],
  },
);
