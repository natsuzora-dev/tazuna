import { addTask, given, scenario } from "./todo.ts";

const arranged = given({ start: "2026-10-25T10:00:00+09:00", records: {}, peers: [] });

export const guardedDeadline = scenario({
  description:
    "Add three tasks at 10:00, one at 12:00, and one at 13:30; at the 11:00 deadline, both hasManyTasks and hasTasks hold for counter, but counter selects the transition of hasManyTasks, the first in written order, and reports many. At the 13:00 deadline, no guard holds, so counter takes no transition and stays in waiting. The task at 13:30 does not make counter reenter waiting or set its deadline again, so counter reports nothing. The deadlines of reminder and counter due at one time fire in either order with the same result",
  given: arranged,
  when: (w) => {
    w.client.send(addTask, { taskId: "task-1" });
    w.client.send(addTask, { taskId: "task-2" });
    w.client.send(addTask, { taskId: "task-3" });
    w.clock.at("2026-10-25T12:00:00+09:00");
    w.client.send(addTask, { taskId: "task-4" });
    w.clock.at("2026-10-25T13:30:00+09:00");
    w.client.send(addTask, { taskId: "task-5" });
    w.clock.at("2026-10-25T15:00:00+09:00");
  },
  then: () => [],
});
