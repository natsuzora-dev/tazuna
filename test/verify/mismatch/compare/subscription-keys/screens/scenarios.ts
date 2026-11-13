import { at, operate, scenario } from "@natsuzora-dev/tazuna";
import { noteScreen } from "./screens.ts";

export const draftAndOpen = scenario("Draft two notes and open the first; no violation", [
  at("2026-10-25T00:00:00Z"),
  operate(noteScreen, "draft"),
  operate(noteScreen, "open"),
]);

export const draftAndOpenWrongKeys = scenario(
  "Same inputs as draftAndOpen; the implementation trace of this scenario opens notesNamed with another prefix and then the note of a key that is not in the bag of notesIn, so verify reports unopenedSubscription, unexpectedSubscription, and Mismatch.renaming",
  [at("2026-10-25T00:00:00Z"), operate(noteScreen, "draft"), operate(noteScreen, "open")],
);
