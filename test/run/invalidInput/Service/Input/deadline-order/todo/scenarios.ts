import { deadline } from "@natsuzora-dev/tazuna";
import { reminder } from "./machines.ts";
import { addTask, scenario } from "./todo.ts";

const given = { start: "2026-10-25T10:00:00+09:00", records: {}, peers: {} } as const;

export const orderWithoutTie = scenario(
  "Add a task at 10:00 and move the clock to 10:30 with an order for the reminder's hour deadline, which is due only at 11:00, so no tie uses the order",
  {
    given,
    when: (w) => {
      w.client.send(addTask, { taskId: "task-1" });
      w.clock.at("2026-10-25T10:30:00+09:00", { order: [deadline(reminder, "waiting", "hour")] });
    },
    then: () => [],
  },
);
