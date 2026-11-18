import { skip } from "@natsuzora-dev/tazuna";
import { todo } from "../todo/contract.ts";
import { scenario } from "./data.ts";
import { noteScreen } from "./screens.ts";

export const draftAndOpen = scenario(
  "Draft two notes and open the first; the screen creates both drafts in one operation and puts their keys in the bag of notesIn, whose elements are equal apart from the keys, so the binding keeps both keys open until the note subscription of the open names the first draft and binds it; no violation",
  {
    given: {
      start: "2026-10-25T00:00:00Z",
      records: { Draft: [] },
      peers: { todo: skip(todo, "verify compares the subscriptions that the screen opens, not their answers") },
    },
    when: (w) => {
      const notes = w.startup.screen(noteScreen);
      w.user.operate(notes, "draft");
      w.user.operate(notes, "open");
    },
    then: () => [],
  },
);
