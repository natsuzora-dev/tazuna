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
  description: "Open the draft screen and a note; the implementation trace never opens the note subscription",
  given: arranged,
  when: (w) => {
    const notes = w.startup.screen(noteScreen);
    w.user.operate(notes, "draft");
    w.user.operate(notes, "open");
  },
  then: () => [],
});
