import { at, mock, scenario, send } from "@natsuzora-dev/tazuna";
import { calendar } from "../calendar/contract.ts";
import { planner } from "./machines.ts";
import { addTask } from "./todo.ts";

const nextDay = { result: "fulfilled", output: { day: "2026-10-26T00:00:00+09:00" } } as const;

export const chosenByContent = scenario(
  "Add a task and answer three times; the first mock, whose input has from 11:00, answers calendar.nextDay#3, whose from is 11:00 whatever its zone, the second, whose input has from 10:00, answers calendar.nextDay#1, and the third mock, without input, answers calendar.nextDay#2, the one request that still waits; the requests' field constructor, which no choice gives, takes no part in the choice",
  [
    at("2026-10-25T10:00:00+09:00"),
    send(addTask, {}),
    mock(planner, [calendar.nextDay, nextDay, { input: { from: "2026-10-25T11:00:00+09:00" } }]),
    mock(planner, [calendar.nextDay, nextDay, { input: { from: "2026-10-25T10:00:00+09:00" } }]),
    mock(planner, [calendar.nextDay, nextDay]),
  ],
);
