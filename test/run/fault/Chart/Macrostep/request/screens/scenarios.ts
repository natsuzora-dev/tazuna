import { at, mock, scenario } from "@natsuzora-dev/tazuna";
import { todo } from "../todo/contract.ts";
import { titledScreen } from "./screens.ts";

export const show = scenario("Answer the shown query, then reject it as unavailable; no violation", [
  at("2026-10-25T09:00:00+09:00"),
  mock(titledScreen, [todo.titled, { result: "fulfilled", output: { titles: ["Buy milk"] } }]),
  mock(titledScreen, [todo.titled, { result: "rejected", rejection: { kind: "unavailable" } }]),
]);
