import { scenario } from "./todo.ts";

export const startsDay = scenario("Start in the morning", {
  given: { start: "2026-10-25T09:00:00+09:00", records: {}, peers: {} },
  when: () => {},
  then: () => [],
});

export const StartsDay = scenario("Start at noon", {
  given: { start: "2026-10-25T12:00:00+09:00", records: {}, peers: {} },
  when: () => {},
  then: () => [],
});
