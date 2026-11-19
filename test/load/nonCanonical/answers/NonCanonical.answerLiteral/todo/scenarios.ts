import { accepted, answered, external, fulfilled, rejected } from "@natsuzora-dev/tazuna";
import { payments } from "../payments/payments.ts";
import { addTask, scenario, taskCount } from "./todo.ts";

export const writesAnswerLiterals = scenario({
  description: "Write each answer as an object literal; check reports answerLiteral for each",
  given: { start: "2026-10-25T10:00:00+09:00", records: { Task: [] }, peers: [external(payments)] },
  when: (w) => {
    w.net.deliver(
      w.peer.payments.answer(w.startup.request(payments.createCharge), {
        result: "accepted",
        output: { chargeId: "ch_1" },
      }),
    );
    return {
      adding: w.client.send(addTask, { taskId: "task-1", title: "Buy milk" }),
      rejectedAdding: w.client.send(addTask, { taskId: "task-2", title: "" }),
      counting: w.client.call(taskCount, {}),
    };
  },
  then: ({ adding, rejectedAdding, counting }) => [
    answered(adding, { result: "accepted" }),
    answered(rejectedAdding, { result: "rejected" as const, rejection: { kind: "invalid-input" } }),
    answered(counting, { result: "fulfilled", output: { count: 0 } }),
  ],
});

export const writesAnswerConstructors = scenario({
  description:
    "Write each answer with its constructor, and a record field named result; check reports nothing, since the record is no answer",
  given: {
    start: "2026-10-25T10:00:00+09:00",
    records: { Task: [{ id: "task-0", title: "Buy eggs", review: { result: "accepted" } }] },
    peers: [external(payments)],
  },
  when: (w) => {
    w.net.deliver(w.peer.payments.answer(w.startup.request(payments.createCharge), accepted({ chargeId: "ch_1" })));
    return {
      adding: w.client.send(addTask, { taskId: "task-1", title: "Buy milk" }),
      rejectedAdding: w.client.send(addTask, { taskId: "task-2", title: "" }),
      counting: w.client.call(taskCount, {}),
    };
  },
  then: ({ adding, rejectedAdding, counting }) => [
    answered(adding, accepted()),
    answered(rejectedAdding, rejected("invalid-input")),
    answered(counting, fulfilled({ count: 0 })),
  ],
});
