import { skip } from "@natsuzora-dev/tazuna";
import { todo } from "../todo/contract.ts";
import { noteScreen, scenario } from "./screens.ts";

export const draftAndOpen = scenario(
  "Draft two notes and open the first; the screen creates both drafts in one operation and puts their keys in the bag of notesIn, whose elements are equal apart from the keys, so verify cannot tell which implementation key stands for the first draft and reports Uncomparable.ambiguous. The subscription stays unpaired, so verify also reports its implementation line as unexpectedSubscription, its end as missingLine and unexpectedLine, and the note subscription of the open, which names the first draft, as Mismatch.request",
  {
    given: {
      start: "2026-10-25T00:00:00Z",
      records: { Draft: [] },
      peers: { todo: skip(todo, "verify compares the subscriptions that the screen opens, not their answers") },
    },
    when: (w) => {
      const notes = w.begin.screen(noteScreen);
      w.user.operate(notes, "draft");
      w.user.operate(notes, "open");
    },
    then: () => [],
  },
);
