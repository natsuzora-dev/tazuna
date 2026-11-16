import { at, scenario } from "@natsuzora-dev/tazuna";

export const start = scenario(
  "Start the service; homeScreen opens counterScreen from -1, and the refinement of the context schema of counterScreen throws, so test reports exception of counterScreen",
  [at("2026-10-25T09:00:00+09:00")],
);
