import { addNote, addTask, contract } from "./notes.ts";

export const notes = contract({ addTask, addNote });
