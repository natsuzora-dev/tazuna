import { closeTasks, scenario } from "./closer.ts";

export const closeOnce = scenario("Close the tasks; test reports assignRead", {
  given: { start: "2026-10-25T09:00:00+09:00", records: {}, peers: [] },
  when: (w) => {
    w.client.send(closeTasks, {});
  },
  then: () => [],
});
