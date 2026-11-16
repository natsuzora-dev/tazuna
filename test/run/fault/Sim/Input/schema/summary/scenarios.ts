import { at, call, scenario } from "@natsuzora-dev/tazuna";
import { itemCount } from "./summary.ts";

export const countItems = scenario("Count the items; no violation", [
  at("2026-10-25T09:00:00+09:00"),
  call(itemCount, { owner: "me" }),
]);
