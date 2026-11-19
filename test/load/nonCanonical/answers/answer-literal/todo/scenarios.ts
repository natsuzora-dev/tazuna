import { accepted, answered, fulfilled, rejected } from "@natsuzora-dev/tazuna";
import { addTask, scenario, taskCount } from "./todo.ts";

export const writesAnswerLiterals = scenario({
  description: "Write each answer as an object literal; check reports answerLiteral for each",
  given: { start: "2026-10-25T10:00:00+09:00", records: { Task: [] }, peers: [] },
  when: (w) => ({
    adding: w.client.send(addTask, { taskId: "task-1", title: "Buy milk" }),
    rejectedAdding: w.client.send(addTask, { taskId: "task-2", title: "" }),
    counting: w.client.call(taskCount, {}),
  }),
  then: ({ adding, rejectedAdding, counting }) => [
    answered(adding, { result: "accepted" }),
    answered(rejectedAdding, { result: "rejected", rejection: { kind: "invalid-input" } }),
    answered(counting, { result: "fulfilled", output: { count: 0 } }),
  ],
});

export const writesAnswerConstructors = scenario({
  description: "Write each answer with its constructor; check reports nothing",
  given: { start: "2026-10-25T10:00:00+09:00", records: { Task: [] }, peers: [] },
  when: (w) => ({
    adding: w.client.send(addTask, { taskId: "task-1", title: "Buy milk" }),
    rejectedAdding: w.client.send(addTask, { taskId: "task-2", title: "" }),
    counting: w.client.call(taskCount, {}),
  }),
  then: ({ adding, rejectedAdding, counting }) => [
    answered(adding, accepted),
    answered(rejectedAdding, rejected("invalid-input")),
    answered(counting, fulfilled({ count: 0 })),
  ],
});
