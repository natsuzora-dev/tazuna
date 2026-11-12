import { entity, service } from "@natsuzora-dev/tazuna";
import { z } from "zod";
import { Task } from "./contract.ts";

export const Note = entity({ description: "A note", fields: { id: z.string() }, key: "id" });

export const { command } = service({ description: "Keep the tasks", entities: { Task } });
const { event } = service({ description: "Keep the notes" });

export const noted = event({});
