import { at, mock, scenario } from "@natsuzora-dev/tazuna";
import { todo } from "../todo/contract.ts";
import { adder } from "./planner.ts";

export const rejectAdd = scenario(
  "Reject the task as already existing; no violation",
  [
    at("2026-10-25T09:00:00+09:00"),
    mock(adder, [todo.addTask, { result: "rejected", rejection: { kind: "already-exists" } }]),
  ],
  { given: { todo: todo.states.milk } },
);

export const rejectLongTitle = scenario(
  "Reject the task with a requires of addTask; the answer fits addTask's contract, and only todo's run, which accepts the short title, gives unproducibleAnswer",
  [
    at("2026-10-25T09:00:00+09:00"),
    mock(adder, [todo.addTask, { result: "rejected", rejection: { kind: "requires", reason: "short" } }]),
  ],
);

export const rejectAddNotFound = scenario(
  "Reject the task as not-found although its input has no ref; addTask cannot answer with that kind, so test reports unlistedRejectionKind",
  [
    at("2026-10-25T09:00:00+09:00"),
    mock(adder, [todo.addTask, { result: "rejected", rejection: { kind: "not-found" } }]),
  ],
);

export const rejectUnknownReason = scenario(
  "Reject the task with the reason long; long is not a requires of addTask, so test reports unlistedRejectionReason",
  [
    at("2026-10-25T09:00:00+09:00"),
    mock(adder, [todo.addTask, { result: "rejected", rejection: { kind: "requires", reason: "long" } }]),
  ],
);
