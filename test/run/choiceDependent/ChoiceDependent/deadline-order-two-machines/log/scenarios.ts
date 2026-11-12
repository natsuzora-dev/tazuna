import { at, scenario } from "@natsuzora-dev/tazuna";

export const waitAnHour = scenario(
  "Wait an hour; the deadlines of ringer and chimer come at one time, ringer fires first as the first in entry order, and the entry that each creates gets its key in the order they come, but entryLogged pairs the keys of the two orders, under which their records are equal, so test reports nothing",
  [at("2026-10-25T09:00:00+09:00"), at("2026-10-25T10:00:00+09:00")],
);
