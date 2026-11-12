import { at, mock, operate, scenario } from "@natsuzora-dev/tazuna";
import { notes } from "../notes/contract.ts";
import { todo } from "../todo/contract.ts";
import { saveScreen } from "./screens.ts";

export const saveBothListingAfterTask = scenario(
  "Save a task and a note; saveScreen shows the tasks only when the task answer comes first, so when the note answer comes first the outputs change, so test reports answerOrder",
  [
    at("2026-10-25T09:00:00+09:00"),
    operate(saveScreen, "save"),
    mock(saveScreen, [todo.saveTask, { result: "accepted" }]),
    mock(saveScreen, [notes.saveNote, { result: "accepted" }, { stale: true }]),
  ],
);
