import { service } from "@natsuzora-dev/tazuna";
import { z } from "zod";

export const { query, contract } = service({ name: "todo", description: "Keep tasks" });

export const tasks = query({ output: { taskIds: z.array(z.string()) } }).resolve(() => ({ taskIds: [] }));
