import { entity, service, singleEntity } from "@natsuzora-dev/tazuna";
import { z } from "zod";

export const Settings = singleEntity({
  description: "The user's settings",
  fields: { theme: z.string().default("light") },
});
export const Task = entity({ description: "A task", fields: { id: z.string() }, key: "id" });

export const { command } = service({
  name: "todo",
  description: "Keep the tasks",
  entities: { settings: Settings, Task },
});
