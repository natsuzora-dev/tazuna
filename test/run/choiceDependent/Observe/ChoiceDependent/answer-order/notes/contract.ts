import { contract } from "@natsuzora-dev/tazuna";
import { saveNote } from "./notes.ts";

export const notes = contract({ saveNote });
