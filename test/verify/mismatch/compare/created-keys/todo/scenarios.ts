import { at, call, scenario, send } from "@natsuzora-dev/tazuna";
import { addTask, seenIds } from "./todo.ts";

export const seenTwice = scenario("Add two tasks and ask twice for the seen ids; no violation", [
  at("2026-10-25T00:00:00Z"),
  send(addTask, { taskId: "task-1" }),
  send(addTask, { taskId: "task-2" }),
  call(seenIds, {}),
  call(seenIds, {}),
]);

export const seenOnce = scenario("Add a task and ask twice for the seen ids; no violation", [
  at("2026-10-25T00:00:00Z"),
  send(addTask, { taskId: "task-1" }),
  call(seenIds, {}),
  call(seenIds, {}),
]);

export const seenTwiceWrongIds = scenario(
  "Same inputs as seenTwice; the implementation trace of this scenario answers the second seenIds with other created keys, so verify reports Mismatch.renaming",
  [
    at("2026-10-25T00:00:00Z"),
    send(addTask, { taskId: "task-1" }),
    send(addTask, { taskId: "task-2" }),
    call(seenIds, {}),
    call(seenIds, {}),
  ],
);

export const seenOnceWrongListed = scenario(
  "Same inputs as seenOnce; the implementation trace of this scenario answers the second seenIds with another key in listed, so verify reports Mismatch.renaming",
  [at("2026-10-25T00:00:00Z"), send(addTask, { taskId: "task-1" }), call(seenIds, {}), call(seenIds, {})],
);
