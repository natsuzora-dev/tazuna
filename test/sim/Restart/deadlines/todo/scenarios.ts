import { at, restart, scenario, send } from "@natsuzora-dev/tazuna";
import { addTask } from "./todo.ts";

export const dueDeadlineFires = scenario(
  "Add a task at 10:00 and restart at 11:00; the 11:00 deadline of waiting is due by the restart, so reminder reports before the restart line",
  [at("2026-10-25T10:00:00+09:00"), send(addTask, {}), at("2026-10-25T11:00:00+09:00"), restart()],
);

export const laterDeadlineDiscarded = scenario(
  "Add a task at 10:00 and restart at 10:30; the restart discards the 11:00 deadline of waiting, and reminder starts again in idle, so nothing reports by 12:00",
  [
    at("2026-10-25T10:00:00+09:00"),
    send(addTask, {}),
    at("2026-10-25T10:30:00+09:00"),
    restart(),
    at("2026-10-25T12:00:00+09:00"),
  ],
);
