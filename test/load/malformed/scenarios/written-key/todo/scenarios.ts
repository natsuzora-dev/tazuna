import { addTask, scenario } from "./todo.ts";

export const givenCreatedKey = scenario({
  description:
    "Given holds a task under todo/Task-1, the form of the first key that todo creates for Task, so loading reports writtenCreatedKey at the scenario",
  given: {
    start: "2026-10-25T10:00:00+09:00",
    records: { Task: [{ id: "todo/Task-1", title: "Buy milk" }] },
    peers: [],
  },
  when: () => ({}),
  then: () => [],
});

export const sentCreatedKey = scenario({
  description:
    "The client sends todo/Task-2 as a task id, the form of a key that todo creates, so loading reports writtenCreatedKey at the line",
  given: { start: "2026-10-25T10:00:00+09:00", records: { Task: [] }, peers: [] },
  when: (w) => {
    w.client.send(addTask, { taskId: "todo/Task-2", title: "Buy milk" });
  },
  then: () => [],
});
