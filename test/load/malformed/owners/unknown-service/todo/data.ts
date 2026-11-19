import { constants, service } from "@natsuzora-dev/tazuna";
import { z } from "zod";

export const { event } = service({ name: "todo", description: "Keep the tasks" });

export const todoConstants = constants({
  service: "tasks",
  schema: z.object({ limit: z.int() }),
  values: { limit: 10 },
});

export const taskAdded = event({});
