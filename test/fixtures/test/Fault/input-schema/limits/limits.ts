import { service } from "@natsuzora-dev/tazuna";
import { z } from "zod";

export const { machine, scenario } = service({ name: "limits", description: "Hold the limit" });

export const limits = machine({
  description: "Hold the limit",
  context: { limit: z.int().min(1).default(1) },
  initial: "holding",
  states: { holding: {} },
}).chart({});
