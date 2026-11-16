import { deadline } from "@natsuzora-dev/tazuna";
import { reminder } from "./machines.ts";
import { addTask, scenario } from "./todo.ts";

const given = { start: "2026-10-25T10:00:00+09:00", records: {}, peers: {} } as const;

export const orderOfFiredDeadline = scenario(
  "Add a task at 10:00, which sets the hour deadlines of reminder and counter for 11:00, and move the clock to 12:00 with an order that names the reminder's deadline twice: it fires first, and the second entry names it again while only the counter's deadline is due",
  {
    given,
    when: (w) => {
      w.client.send(addTask, { taskId: "task-1" });
      w.clock.at("2026-10-25T12:00:00+09:00", {
        order: [deadline(reminder, "waiting", "hour"), deadline(reminder, "waiting", "hour")],
      });
    },
    then: () => [],
  },
);
