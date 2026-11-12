import { at, scenario, send } from "@natsuzora-dev/tazuna";
import { addNote } from "./notes.ts";

export const addOne = scenario(
  "Add a note; addNote decides noteDrafted, which notes.ts does not export, so it is no definition of the spec and test reports unlistedEmittedEvent with event null",
  [at("2026-10-25T09:00:00+09:00"), send(addNote, { noteId: "note-1" })],
);
