import { run, type SingleRequestLine, type When } from "@natsuzora-dev/tazuna";
import { notifier } from "../notifier/contract.ts";
import { addTask, scenario, taskAdded, taskCount } from "./todo.ts";

const peers = { notifier: run(notifier, { OpenTask: [] }) } as const;
const given = { start: "2026-10-25T09:00:00+09:00", records: { Task: [] }, peers } as const;

/** The network delivers todo's taskAdded, which `line` caused, to notifier. */
const delivered = (w: When<typeof peers>, line: SingleRequestLine) => w.net.deliver(line.event(taskAdded));

export const resent = scenario(
  "Send addTask twice with the same id and the same input; todo does not process the second and answers it again with the first answer",
  {
    given,
    when: (w) => {
      const first = w.client.send(addTask, { taskId: "task-1", title: "Buy milk" });
      delivered(w, first);
      w.client.resend(first);
    },
    then: () => [],
  },
);

export const changedInput = scenario(
  "Send addTask, again with the same id and another input, and again with the first input; todo rejects the second with reused-id and answers the third again with the first answer",
  {
    given,
    when: (w) => {
      const first = w.client.send(addTask, { taskId: "task-1", title: "Buy milk" });
      delivered(w, first);
      w.client.send(addTask, { taskId: "task-1", title: "Buy eggs" }, { sameIdAs: first });
      w.client.resend(first);
    },
    then: () => [],
  },
);

export const correctedInput = scenario(
  "Send addTask with an input that does not fit the schema, then with the same id and the input fixed; todo rejects the first with invalid-input and does not keep the rejection as the answer of that id, so it processes the second",
  {
    given,
    when: (w) => {
      const first = w.client.send(addTask, { taskId: "task-1", title: "" });
      const fixed = w.client.send(addTask, { taskId: "task-1", title: "Buy milk" }, { sameIdAs: first });
      delivered(w, fixed);
    },
    then: () => [],
  },
);

export const askedTwice = scenario(
  "Ask for taskCount, add a task, and ask again with the same id; todo processes both queries and answers the second with the count after addTask",
  {
    given,
    when: (w) => {
      const first = w.client.call(taskCount, {});
      const add = w.client.send(addTask, { taskId: "task-1", title: "Buy milk" });
      delivered(w, add);
      w.client.resend(first);
    },
    then: () => [],
  },
);
