import { service } from "@natsuzora-dev/tazuna";
import { z } from "zod";

export const { machine } = service({ name: "counters", description: "Count per tag" });

export const tagCounter = machine({
  description: "Count the visits of each tag, starting below the minimum",
  initial: "counting",
  states: {
    counting: {
      type: "map",
      key: { tag: z.string() },
      context: { visits: z.int().min(1).default(0) },
      initial: "idle",
      states: { idle: {} },
    },
  },
}).chart({ states: { counting: { items: () => [{ tag: "home" }] } } });
