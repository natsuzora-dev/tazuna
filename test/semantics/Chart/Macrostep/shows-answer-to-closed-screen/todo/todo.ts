import { service } from "@natsuzora-dev/tazuna";
import { z } from "zod";

export const { query } = service({ description: "Keep tasks" });

export const tasks = query({
  output: { taskIds: z.array(z.string()) },
  requires: { isListed: () => false },
}).resolve(() => ({ taskIds: [] }));
