import { externalService } from "@natsuzora-dev/tazuna";
import { z } from "zod";

export const { command, query } = externalService({ description: "Keep the tasks" });

export const saveTask = command({
  input: { title: z.string() },
  emits: [],
  rejects: ["invalid-input", "requires", "unavailable", "reused-id"],
});

export const tasks = query({
  output: { titles: z.array(z.string()) },
  rejects: ["invalid-input", "requires", "unavailable"],
});
