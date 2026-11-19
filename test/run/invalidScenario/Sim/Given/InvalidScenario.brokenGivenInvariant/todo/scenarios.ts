import { scenario } from "./todo.ts";

export const untitled = scenario({
  description: "Given writes a task without a title, which the invariant titled of Task forbids",
  given: { start: "2026-10-25T09:00:00+09:00", records: { Task: [{ id: "task-1", title: "" }] }, peers: [] },
  when: () => {},
  then: () => [],
});
