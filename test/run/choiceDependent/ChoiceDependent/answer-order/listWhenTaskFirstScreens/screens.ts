import { notes } from "../notes/contract.ts";
import { todo } from "../todo/contract.ts";
import { screen } from "./data.ts";

export const saveScreen = screen({
  description: "Save a task and a note, and show the tasks once the task is saved first",
  queries: { tasks: todo.tasks },
  commands: { saveTask: todo.saveTask, saveNote: notes.saveNote },
  controls: { save: { label: "Save" }, back: { label: "Back" } },
  initial: "editing",
  states: { editing: {}, saving: {}, listing: {}, noting: {} },
}).chart({
  states: {
    editing: { on: { save: [{ target: "saving" }] } },
    saving: {
      sends: {
        saveTask: { input: () => ({ title: "Buy milk" }), onAccepted: [{ target: "listing" }], onRejected: [] },
        saveNote: { input: () => ({ text: "Milk" }), onAccepted: [{ target: "noting" }], onRejected: [] },
      },
    },
    listing: { on: { back: [{ target: "editing" }] }, shows: { tasks: {} } },
    noting: { on: { back: [{ target: "editing" }] } },
  },
});
