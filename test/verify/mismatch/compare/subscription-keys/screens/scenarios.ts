import { skip } from "@natsuzora-dev/tazuna";
import { todo } from "../todo/contract.ts";
import { given, scenario } from "./data.ts";
import { noteScreen } from "./screens.ts";

const arranged = given({
  start: "2026-10-25T00:00:00Z",
  records: { Draft: [] },
  peers: [skip(todo, "verify compares the subscriptions that the screen opens, not their answers")],
});

export const draftAndOpen = scenario({
  description: "Draft two notes and open the first; no violation",
  given: arranged,
  when: (w) => {
    const notes = w.startup.screen(noteScreen);
    w.user.operate(notes, "draft");
    w.user.operate(notes, "open");
  },
  then: () => [],
});

export const draftAndOpenWrongKeys = scenario({
  description:
    "Same inputs as draftAndOpen; the implementation trace of this scenario opens no notesNamed subscription at the start, so its end is missing too, creates the drafts in the other order, opens the note of the second draft, and opens notesNamed with another prefix at the end, so verify reports unopenedSubscription, missingLine, Mismatch.request, and unexpectedSubscription",
  given: arranged,
  when: (w) => {
    const notes = w.startup.screen(noteScreen);
    w.user.operate(notes, "draft");
    w.user.operate(notes, "open");
  },
  then: () => [],
});
