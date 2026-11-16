import { contract } from "@natsuzora-dev/tazuna";
import { addNote, addTask } from "./notes.ts";

export const notes = contract({ addTask, addNote });
