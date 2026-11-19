import { addTask, given, scenario } from "./todo.ts";

const arranged = given({ start: "2026-10-25T10:00:00+09:00", records: {}, peers: [] });

export const dueDeadlineFires = scenario(
  "Add a task at 10:00 and restart at 11:00; the 11:00 deadline of waiting is due by the restart, so reminder reports before the restart line",
  {
    given: arranged,
    when: (w) => {
      w.client.send(addTask, {});
      w.clock.at("2026-10-25T11:00:00+09:00");
      w.host.restart();
    },
    then: () => [],
  },
);

export const laterDeadlineDiscarded = scenario(
  "Add a task at 10:00 and restart at 10:30; the restart discards the 11:00 deadline of waiting, and reminder starts again in idle, so nothing reports by 12:00",
  {
    given: arranged,
    when: (w) => {
      w.client.send(addTask, {});
      w.clock.at("2026-10-25T10:30:00+09:00");
      w.host.restart();
      w.clock.at("2026-10-25T12:00:00+09:00");
    },
    then: () => [],
  },
);
