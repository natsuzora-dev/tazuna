import { service } from "@natsuzora-dev/tazuna";
import { z } from "zod";
import { notes } from "../notes/contract.ts";

export const { query, screen } = service({ description: "Show the notes" });

export const shown = query({ output: { open: z.boolean() } }).resolve(() => ({ open: true }));

export const boardScreen = screen({
  description: "A screen that shows the notes",
  queries: { noteList: notes.noteList },
  initial: "listing",
  states: { listing: {} },
}).chart({ states: { listing: { shows: { noteList: {} } } } });
