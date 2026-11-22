import { parseInstant } from "@natsuzora-dev/tazuna";
import { scenario } from "./todo.ts";

export const start = scenario({
  description:
    "Start the service; counter sends count on every counted without a guard, which makes a chain of more than 100 commands, so test reports exceededCommandDepth",
  given: { start: parseInstant("2026-10-25T09:00:00+09:00"), records: { Counter: { value: 0 } }, peers: [] },
  when: (_w) => {},
  then: () => [],
});
