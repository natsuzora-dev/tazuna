import { parseInstant, run } from "@natsuzora-dev/tazuna";
import { notifier } from "../notifier/contract.ts";
import { addTask, scenario } from "./todo.ts";

export const notifyWithoutDevice = scenario({
  description: "Add a task, which notifies notifier, whose run asks device for a permission, which Given does not list",
  given: { start: parseInstant("2026-10-25T09:00:00+09:00"), records: {}, peers: [run(notifier, {})] },
  when: (w) => {
    const add = w.client.send(addTask, { taskId: "task-1" });
    w.net.deliver(add.request(notifier.notify));
  },
  then: () => [],
});
