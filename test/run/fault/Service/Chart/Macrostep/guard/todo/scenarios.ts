import { addTask, scenario } from "./todo.ts";

export const addUntitled = scenario(
  "Add a task without a title; the guard titled of watcher throws, so test reports exception of watcher",
  {
    given: { start: "2026-10-25T09:00:00+09:00", records: {}, peers: {} },
    when: (w) => {
      w.client.send(addTask, { title: "" });
    },
    then: () => [],
  },
);
