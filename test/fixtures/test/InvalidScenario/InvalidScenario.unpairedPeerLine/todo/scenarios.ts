import { accepted, parseInstant, run } from "@natsuzora-dev/tazuna";
import { notifier } from "../notifier/contract.ts";
import { addTask, scenario } from "./todo.ts";

export const notifierAddsTask = scenario({
  description: "Add a task, which notifies notifier, and state that notifier sends addTask, which its run never sends",
  given: { start: parseInstant("2026-10-25T09:00:00+09:00"), records: {}, peers: [run(notifier, {})] },
  when: (w) => {
    const add = w.client.as("client").send(addTask, { taskId: "task-1" });
    const notifying = w.net.deliver(add.request(notifier.notify));
    w.net.deliver(w.peer.notifier.answer(notifying, accepted()));
    w.peer.notifier.send(addTask, { taskId: "task-2" });
  },
  then: () => [],
});
