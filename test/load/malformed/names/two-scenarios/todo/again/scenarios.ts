import { scenario } from "../todo.ts";

export const startsDay = scenario("Start at noon", {
  given: { start: "2026-10-25T12:00:00+09:00", records: {}, peers: {} },
  when: () => {},
  then: () => [],
});
