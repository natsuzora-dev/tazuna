import { at, scenario } from "@natsuzora-dev/tazuna";

export const startsDay = scenario("Start at noon", [at("2026-10-25T12:00:00+09:00")]);
