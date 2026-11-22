import { external, parseInstant } from "@natsuzora-dev/tazuna";
import { device } from "../device/contract.ts";
import { addTask, given, scenario } from "./todo.ts";

export const emptyTitle = scenario({
  description:
    "Add a task with an empty title, which the input schema of addTask does not allow; todo rejects it with invalid-input",
  given: given({ start: parseInstant("2026-10-25T10:00:00+09:00"), records: { Task: [] }, peers: [external(device)] }),
  when: (w) => {
    w.client.send(addTask, { taskId: "task-1", title: "" });
  },
  then: () => [],
});
