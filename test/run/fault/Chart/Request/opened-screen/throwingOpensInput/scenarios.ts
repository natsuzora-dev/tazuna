import { at, scenario } from "@natsuzora-dev/tazuna";

export const start = scenario(
  "Start the service; the opens input of homeScreen for pickScreen throws, so test reports exception of homeScreen",
  [at("2026-10-25T09:00:00+09:00")],
);
