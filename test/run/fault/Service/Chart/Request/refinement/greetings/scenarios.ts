import { at, scenario } from "@natsuzora-dev/tazuna";

export const start = scenario(
  "Start the service; greeter sends greet with an empty name, and the refinement of the input schema of greet throws, so test reports exception of greet",
  [at("2026-10-25T09:00:00+09:00")],
);
