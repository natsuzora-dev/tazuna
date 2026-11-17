import { constants, service } from "@natsuzora-dev/tazuna";
import { z } from "zod";

export const { event } = service({ name: "todo", description: "Keep the tasks" });

export const todoConstants = constants("tasks", z.object({ limit: z.int() }), { limit: 10 });

export const taskAdded = event({});
