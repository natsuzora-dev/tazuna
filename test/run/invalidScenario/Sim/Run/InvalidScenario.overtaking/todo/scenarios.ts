import { run } from "@natsuzora-dev/tazuna";
import { listener } from "../listener/contract.ts";
import { addTask, noted, scenario } from "./todo.ts";

export const secondNoteFirst = scenario({
  description:
    "Add two tasks, each of which todo notes, and deliver the second noted while the first is in flight on the same channel",
  given: { start: "2026-10-25T09:00:00+09:00", records: {}, peers: [run(listener, {})] },
  when: (w) => {
    w.client.send(addTask, { taskId: "task-1" });
    const second = w.client.send(addTask, { taskId: "task-2" });
    w.net.deliver(second.event(noted));
  },
  then: () => [],
});
