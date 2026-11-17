import { service, singleEntity } from "@natsuzora-dev/tazuna";
import { z } from "zod";

export const Stats = singleEntity({
  description: "Statistics of tasks, whose goal default throws",
  fields: {
    goal: z.number().default(() => {
      throw new Error("no goal is set");
    }),
  },
});

export const { command } = service({ name: "stats", description: "Keep the statistics", entities: { Stats } });
