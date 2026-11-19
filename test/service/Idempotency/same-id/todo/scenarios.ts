import { run } from "@natsuzora-dev/tazuna";
import { notifier } from "../notifier/contract.ts";
import { addTask, given, scenario, taskAdded, taskCount } from "./todo.ts";

const arranged = given({
  start: "2026-10-25T09:00:00+09:00",
  records: { Task: [] },
  peers: [run(notifier, { OpenTask: [] })],
});

export const resent = scenario(
  "Send addTask twice with the same id and the same input; todo does not process the second and answers it again with the first answer",
  {
    given: arranged,
    when: (w) => {
      const first = w.client.send(addTask, { taskId: "task-1", title: "Buy milk" });
      w.net.deliver(first.event(taskAdded));
      w.client.resend(first);
    },
    then: () => [],
  },
);

export const changedInput = scenario(
  "Send addTask, again with the same id and another input, and again with the first input; todo rejects the second with reused-id and answers the third again with the first answer",
  {
    given: arranged,
    when: (w) => {
      const first = w.client.send(addTask, { taskId: "task-1", title: "Buy milk" });
      w.net.deliver(first.event(taskAdded));
      w.client.send(addTask, { taskId: "task-1", title: "Buy eggs" }, { sameIdAs: first });
      w.client.resend(first);
    },
    then: () => [],
  },
);

export const reorderedInput = scenario(
  "Send addTask, and again with the same id and the same input written in another field order; todo answers the second again with the first answer, since an input is the same whatever the order of its fields",
  {
    given: arranged,
    when: (w) => {
      const first = w.client.send(addTask, { taskId: "task-1", title: "Buy milk" });
      w.net.deliver(first.event(taskAdded));
      w.client.send(addTask, { title: "Buy milk", taskId: "task-1" }, { sameIdAs: first });
    },
    then: () => [],
  },
);

export const correctedInput = scenario(
  "Send addTask with an input that does not fit the schema, then with the same id and the input fixed; todo rejects the first with invalid-input and does not keep the rejection as the answer of that id, so it processes the second",
  {
    given: arranged,
    when: (w) => {
      const first = w.client.send(addTask, { taskId: "task-1", title: "" });
      const fixed = w.client.send(addTask, { taskId: "task-1", title: "Buy milk" }, { sameIdAs: first });
      w.net.deliver(fixed.event(taskAdded));
    },
    then: () => [],
  },
);

export const askedTwice = scenario(
  "Ask for taskCount, add a task, and ask again with the same id; todo processes both queries and answers the second with the count after addTask",
  {
    given: arranged,
    when: (w) => {
      const first = w.client.call(taskCount, {});
      const add = w.client.send(addTask, { taskId: "task-1", title: "Buy milk" });
      w.net.deliver(add.event(taskAdded));
      w.client.resend(first);
    },
    then: () => [],
  },
);
