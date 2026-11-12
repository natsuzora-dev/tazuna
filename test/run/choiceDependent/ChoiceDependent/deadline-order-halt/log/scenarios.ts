import { at, scenario } from "@natsuzora-dev/tazuna";

export const waitAnHour = scenario(
  "Wait an hour; the deadlines of ringer and chimer come at one time, ringer fires first as the first in entry order, and addEntry throws when the ring is not the first entry, so the order with chimer first halts and test reports deadlineOrder",
  [at("2026-10-25T09:00:00+09:00"), at("2026-10-25T10:00:00+09:00")],
);
