import { at, scenario } from "@natsuzora-dev/tazuna";

export const start = scenario(
  "Start the service; the default limit 0 is below the minimum 1 of the context schema, so test reports initialContextSchema",
  [at("2026-10-25T09:00:00+09:00")],
);
