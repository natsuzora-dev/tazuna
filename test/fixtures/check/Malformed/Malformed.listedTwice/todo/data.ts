import { service } from "@natsuzora-dev/tazuna";
import { Task } from "./contract.ts";

export const { command } = service({ name: "todo", description: "Keep the tasks", entities: { Task } });
