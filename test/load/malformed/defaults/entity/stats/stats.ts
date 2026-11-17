import { service, singleEntity } from "@natsuzora-dev/tazuna";
import { z } from "zod";

export const Stats = singleEntity({
  description: "Statistics of tasks, starting below the minimum",
  fields: { completed: z.number().min(1).default(0) },
});

export const { command } = service({ name: "stats", description: "Keep the statistics", entities: { Stats } });
