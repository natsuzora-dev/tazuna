import { scenario } from "./todo.ts";

export const start = scenario("Start the service; test reports exceededOnDoneSelections", {
  given: { start: "2026-10-25T09:00:00+09:00", records: {}, peers: {} },
  when: (_w) => {},
  then: () => [],
});
