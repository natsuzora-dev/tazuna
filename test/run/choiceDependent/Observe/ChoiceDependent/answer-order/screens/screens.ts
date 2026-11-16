import { any } from "@natsuzora-dev/tazuna";
import { z } from "zod";
import { notes } from "../notes/contract.ts";
import { todo } from "../todo/contract.ts";
import { screen } from "./data.ts";

export const saveScreen = screen({
  description: "Save a task and a note, and show the tasks once both are saved",
  queries: { tasks: todo.tasks },
  commands: { saveTask: todo.saveTask, saveNote: notes.saveNote },
  controls: {
    save: { label: "Save" },
    back: { label: "Back" },
    rename: { label: "Rename", payload: { title: z.string() } },
  },
  initial: "editing",
  states: {
    editing: {},
    saving: {
      type: "parallel",
      states: {
        task: { initial: "taskSaving", states: { taskSaving: {}, taskSaved: { type: "final" } } },
        note: { initial: "noteSaving", states: { noteSaving: {}, noteSaved: { type: "final" } } },
      },
    },
    listing: {},
  },
}).chart({
  offers: { save: any, back: any, rename: any },
  states: {
    editing: { on: { save: [{ target: "saving" }], rename: [] } },
    saving: { on: { rename: [] }, onDone: [{ target: "listing" }] },
    taskSaving: {
      sends: {
        saveTask: { input: () => ({ title: "Buy milk" }), onAccepted: [{ target: "taskSaved" }], onRejected: [] },
      },
    },
    noteSaving: {
      sends: { saveNote: { input: () => ({ text: "Milk" }), onAccepted: [{ target: "noteSaved" }], onRejected: [] } },
    },
    listing: { on: { back: [{ target: "editing" }] }, shows: { tasks: {} } },
  },
});
