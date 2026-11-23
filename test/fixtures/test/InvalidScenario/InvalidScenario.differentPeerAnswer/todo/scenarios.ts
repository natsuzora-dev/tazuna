import { parseInstant, rejected, run } from "@natsuzora-dev/tazuna";
import { notifier } from "../notifier/contract.ts";
import { addTask, scenario } from "./todo.ts";

export const rejectedNotify = scenario({
  description: "Add a task, which notifies notifier, and state that notifier rejects notify, though its run accepts it",
  given: { start: parseInstant("2026-10-25T09:00:00+09:00"), records: {}, peers: [run(notifier, {})] },
  when: (w) => {
    const add = w.client.as("client").send(addTask, { taskId: "task-1" });
    const notifying = w.net.deliver(add.request(notifier.notify));
    w.net.deliver(w.peer.notifier.answer(notifying, rejected("unavailable")));
  },
  then: () => [],
});
