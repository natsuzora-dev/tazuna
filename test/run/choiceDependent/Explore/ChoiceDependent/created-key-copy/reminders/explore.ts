import { domain, explore } from "@natsuzora-dev/tazuna";
import { add } from "./reminders.ts";

export const remindersExplore = explore({
  service: "reminders",
  depth: 2,
  domains: [domain(add.input.id, ["a"]), domain(add.input.text, ["a"])],
});
