import { service } from "@natsuzora-dev/tazuna";
import { Task } from "../todo/contract.ts";

export const { event } = service({ description: "Keep the notes on tasks", entities: { Task } });
