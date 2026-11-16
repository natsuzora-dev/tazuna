import { at, scenario } from "@natsuzora-dev/tazuna";

export const start = scenario(
  "Start the service; the set picked holds the element a twice, so test reports contextSchema",
  [at("2026-10-25T09:00:00+09:00")],
);
