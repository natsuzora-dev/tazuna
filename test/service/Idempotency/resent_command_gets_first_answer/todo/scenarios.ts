import { parseInstant, run } from "@natsuzora-dev/tazuna";
import { notifier } from "../notifier/contract.ts";
import { addTask, given, scenario, taskAdded } from "./todo.ts";

const arranged = given({
  start: parseInstant("2026-10-25T09:00:00+09:00"),
  records: { Task: [] },
  peers: [run(notifier, { OpenTask: [] })],
});

export const resent = scenario({
  description:
    "Send addTask twice with the same id and the same input; todo does not process the second and answers it again with the first answer",
  given: arranged,
  when: (w) => {
    const first = w.client.send(addTask, { taskId: "task-1", title: "Buy milk" });
    w.net.deliver(first.event(taskAdded));
    w.client.resend(first);
  },
  then: () => [],
});

export const reorderedInput = scenario({
  description:
    "Send addTask, and again with the same id and the same input written in another field order; todo answers the second again with the first answer, since an input is the same whatever the order of its fields",
  given: arranged,
  when: (w) => {
    const first = w.client.send(addTask, { taskId: "task-1", title: "Buy milk" });
    w.net.deliver(first.event(taskAdded));
    w.client.send(addTask, { title: "Buy milk", taskId: "task-1" }, { sameIdAs: first });
  },
  then: () => [],
});
