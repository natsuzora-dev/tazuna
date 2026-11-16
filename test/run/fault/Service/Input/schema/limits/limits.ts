import { service } from "@natsuzora-dev/tazuna";
import { z } from "zod";

export const { machine } = service({ description: "Hold the limit" });

export const limits = machine({
  description: "Hold the limit",
  context: { limit: z.number().min(1).default(1) },
  initial: "holding",
  states: { holding: {} },
}).chart({});
