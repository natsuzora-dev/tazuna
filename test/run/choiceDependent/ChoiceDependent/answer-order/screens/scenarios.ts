import { at, mock, operate, scenario } from "@natsuzora-dev/tazuna";
import { notes } from "../notes/contract.ts";
import { todo } from "../todo/contract.ts";
import { saveScreen } from "./screens.ts";

export const saveBoth = scenario("Save a task and a note; no violation", [
  at("2026-10-25T09:00:00+09:00"),
  operate(saveScreen, "save"),
  mock(saveScreen, [todo.saveTask, { result: "accepted" }]),
  mock(saveScreen, [notes.saveNote, { result: "accepted" }]),
]);

export const saveOnly = scenario("Save a task and a note, and leave both answers to `tazuna test`; no violation", [
  at("2026-10-25T09:00:00+09:00"),
  operate(saveScreen, "save"),
]);
