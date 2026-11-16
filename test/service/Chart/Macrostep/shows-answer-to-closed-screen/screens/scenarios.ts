import { at, mock, scenario } from "@natsuzora-dev/tazuna";
import { todo } from "../todo/contract.ts";
import { listScreen } from "./listScreen.ts";

export const answerToClosedScreen = scenario(
  "Answer the subscription at 11:00; listScreen opens at 10:00 and subscribes to todo.tasks. The subscription has not ended yet when the answer arrives, so the mock has no stale. listScreen enters closed through an always transition and closes before it processes the answer, so the subscription ends and the answer does not reach listScreen. The answer is a rejection that blames the caller, but it reaches no closed screen, so no rejection is reported",
  [
    at("2026-10-25T10:00:00+09:00"),
    at("2026-10-25T11:00:00+09:00"),
    mock(listScreen, [todo.tasks, { result: "rejected", rejection: { kind: "requires", reason: "isListed" } }]),
  ],
);
