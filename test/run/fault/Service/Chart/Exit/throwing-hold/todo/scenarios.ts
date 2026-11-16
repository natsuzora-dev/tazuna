import { scenario } from "./todo.ts";

export const start = scenario(
  "Start the service; watcher reads its held task, whose hold throws because there is no task, so test reports exception of watcher",
  {
    given: { start: "2026-10-25T09:00:00+09:00", records: { Task: [] }, peers: {} },
    when: (_w) => {},
    then: () => [],
  },
);
