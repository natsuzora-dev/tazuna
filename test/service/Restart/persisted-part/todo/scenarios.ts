import { at, call, restart, scenario, send, subscribe } from "@natsuzora-dev/tazuna";
import { addTask, taskCount } from "./todo.ts";

export const recordsStay = scenario(
  "Add t1 with the id add-1, restart, call taskCount, and send add-1 again; the record of t1 stays, so taskCount answers 1, and the kept answer of add-1 answers the resent command without a second taskAdded",
  [
    at("2026-10-25T10:00:00+09:00"),
    send(addTask, { taskId: "t1" }, { id: "add-1" }),
    at("2026-10-25T10:05:00+09:00"),
    restart(),
    call(taskCount, {}),
    send(addTask, { taskId: "t1" }, { id: "add-1" }),
  ],
);

export const subscriptionsEnd = scenario(
  "Subscribe to taskCount with the id s1, restart, and add t1; the restart drops the subscription, so adding t1 sends no answer to s1",
  [at("2026-10-25T10:00:00+09:00"), subscribe(taskCount, {}, { id: "s1" }), restart(), send(addTask, { taskId: "t1" })],
);
