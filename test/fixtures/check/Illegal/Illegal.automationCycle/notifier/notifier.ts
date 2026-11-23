import { emit } from "@natsuzora-dev/tazuna";
import { todo } from "../todo/contract.ts";
import { automation, command } from "./data.ts";
import { noticed } from "./events.ts";

export const notice = command({ callers: ["client", "notifier"], emits: [noticed] }).decide(() => [emit(noticed, {})]);

export const noticeAdded = automation({
  receives: { added: todo.added },
  commands: { notice },
}).send({});
