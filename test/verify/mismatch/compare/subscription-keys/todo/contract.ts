import { contract } from "@natsuzora-dev/tazuna";
import { note, notesIn, notesNamed } from "./todo.ts";

export const todo = contract({ notesIn, note, notesNamed });
