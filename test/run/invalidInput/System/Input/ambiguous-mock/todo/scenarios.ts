import { at, mock, scenario, send } from "@natsuzora-dev/tazuna";
import { calendar } from "../calendar/contract.ts";
import { planner } from "./machines.ts";
import { addTask } from "./todo.ts";

const nextDay = { result: "fulfilled", output: { day: "2026-10-26T00:00:00+09:00" } } as const;

export const answersWithoutInput = scenario(
  "Add a task and answer once without input; planner waits on three requests with different inputs, and no written order chooses one, so test reports ambiguousMock",
  [at("2026-10-25T10:00:00+09:00"), send(addTask, {}), mock(planner, [calendar.nextDay, nextDay])],
);

export const answersByZone = scenario(
  "Add a task and answer once with the zone that all three requests have; the zone does not tell them apart, so test reports ambiguousMock",
  [
    at("2026-10-25T10:00:00+09:00"),
    send(addTask, {}),
    mock(planner, [calendar.nextDay, nextDay, { input: { zone: "Asia/Tokyo" } }]),
  ],
);
