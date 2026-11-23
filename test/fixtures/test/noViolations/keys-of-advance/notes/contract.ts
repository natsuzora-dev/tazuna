import { addNote, addTask, contract, noteByLabel } from "./notes.ts";

export const notes = contract({ addTask, addNote, noteByLabel });
