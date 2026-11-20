import { addTask, completeTask, given, scenario } from "./todo.ts";

const arranged = given({ start: "2026-10-25T10:00:00+09:00", records: {}, peers: [] });

export const completedInTime = scenario({
  description:
    "Add a task at 10:00, complete it at 10:30, and add another at 12:00; reminder exits waiting at 10:30, which cancels the 11:00 deadline, and notifies at the 13:00 deadline of waiting, which it reentered at 12:00",
  given: arranged,
  when: (w) => {
    w.client.send(addTask, { taskId: "task-1" });
    w.clock.at("2026-10-25T10:30:00+09:00");
    w.client.send(completeTask, { taskId: "task-1" });
    w.clock.at("2026-10-25T12:00:00+09:00");
    w.client.send(addTask, { taskId: "task-2" });
    w.clock.at("2026-10-25T13:30:00+09:00");
  },
  then: () => [],
});
