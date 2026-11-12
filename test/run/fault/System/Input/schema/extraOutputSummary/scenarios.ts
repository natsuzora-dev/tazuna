import { at, call, scenario } from "@natsuzora-dev/tazuna";
import { itemCount } from "./summary.ts";

export const countItems = scenario(
  "Count the items; itemCount returns the input field owner, which its output schema does not have, so test reports outputSchema",
  [at("2026-10-25T09:00:00+09:00"), call(itemCount, { owner: "me" })],
);
