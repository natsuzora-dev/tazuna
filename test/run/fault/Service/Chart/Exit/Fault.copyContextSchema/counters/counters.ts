import { service } from "@natsuzora-dev/tazuna";
import { z } from "zod";

export const { machine, scenario } = service({ name: "counters", description: "Count per tag" });

export const tagCounter = machine({
  description: "Count the visits of each tag, and set the count below the minimum when a copy starts",
  initial: "counting",
  states: {
    counting: {
      type: "map",
      key: { tag: z.string() },
      context: { visits: z.int().min(1).default(1) },
      initial: "idle",
      states: { idle: {} },
    },
  },
}).chart({
  states: { counting: { items: () => [{ tag: "home" }] }, idle: { entry: { assign: { visits: () => 0 } } } },
});
