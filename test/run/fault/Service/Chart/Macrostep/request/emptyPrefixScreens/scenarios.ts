import { at, mock, scenario } from "@natsuzora-dev/tazuna";
import { todo } from "../todo/contract.ts";
import { titledScreen } from "./screens.ts";

export const show = scenario(
  "Reject the shown query with requires; titledScreen shows titled with an empty prefix, and a rejection other than unavailable fails it, so test reports rejectedShows",
  [
    at("2026-10-25T09:00:00+09:00"),
    mock(titledScreen, [todo.titled, { result: "rejected", rejection: { kind: "requires", reason: "notEmpty" } }]),
  ],
);
