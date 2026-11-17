import { skip } from "@natsuzora-dev/tazuna";
import { todo } from "../todo/contract.ts";
import { noteScreen, scenario } from "./screens.ts";

const given = {
  start: "2026-10-25T00:00:00Z",
  records: { Draft: [] },
  peers: { todo: skip(todo, "verify compares the subscriptions that the screen opens, not their answers") },
} as const;

export const draftAndOpen = scenario("Draft two notes and open the first; no violation", {
  given,
  when: (w) => {
    const notes = w.startup.screen(noteScreen);
    w.user.operate(notes, "draft");
    w.user.operate(notes, "open");
  },
  then: () => [],
});

export const draftAndOpenWrongKeys = scenario(
  "Same inputs as draftAndOpen; the implementation trace of this scenario opens no notesNamed subscription at the start, so its end is missing too, creates the drafts in the other order, opens the note of the second draft, and opens notesNamed with another prefix at the end, so verify reports unopenedSubscription, missingLine, Mismatch.request, and unexpectedSubscription",
  {
    given,
    when: (w) => {
      const notes = w.startup.screen(noteScreen);
      w.user.operate(notes, "draft");
      w.user.operate(notes, "open");
    },
    then: () => [],
  },
);
