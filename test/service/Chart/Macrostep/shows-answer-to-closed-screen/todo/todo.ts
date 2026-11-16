import { externalService } from "@natsuzora-dev/tazuna";
import { z } from "zod";

export const { query, contract } = externalService({ description: "Keep tasks" });

export const tasks = query({
  output: { taskIds: z.array(z.string()) },
  rejects: ["requires"],
  requires: { isListed: () => false },
});
