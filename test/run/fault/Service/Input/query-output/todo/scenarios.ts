import { scenario, taskCount } from "./todo.ts";

export const countNone = scenario(
  "Count the tasks while there is none; the refinement of the output schema of taskCount throws, so test reports exception of taskCount",
  {
    given: { start: "2026-10-25T09:00:00+09:00", records: { Task: [] }, peers: [] },
    when: (w) => {
      w.client.call(taskCount, {});
    },
    then: () => [],
  },
);
