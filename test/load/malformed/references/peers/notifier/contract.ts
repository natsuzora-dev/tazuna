import { at, contract, mock, receive } from "@natsuzora-dev/tazuna";
import { todo } from "../todo/contract.ts";
import { announce, announceAdded } from "./notifier.ts";

export const notifier = contract({
  announce,
  states: {
    announcedMilk: [at("2026-10-25T08:00:00+09:00"), receive(todo.taskAdded, { taskId: "task-1" })],
    addedMilk: [at("2026-10-25T08:00:00+09:00"), mock(announceAdded, [todo.addTask, { result: "accepted" }])],
  },
});
