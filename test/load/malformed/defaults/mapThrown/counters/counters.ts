import { service } from "@natsuzora-dev/tazuna";
import { z } from "zod";

export const { machine } = service({ name: "counters", description: "Count per tag" });

export const tagCounter = machine({
  description: "Count the visits of each tag, whose default throws",
  initial: "counting",
  states: {
    counting: {
      type: "map",
      key: { tag: z.string() },
      context: {
        visits: z.number().default(() => {
          throw new Error("no visit count is set");
        }),
      },
      initial: "idle",
      states: { idle: {} },
    },
  },
}).chart({ states: { counting: { items: () => [{ tag: "home" }] } } });
