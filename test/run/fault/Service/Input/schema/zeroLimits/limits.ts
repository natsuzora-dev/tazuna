import { service } from "@natsuzora-dev/tazuna";
import { z } from "zod";

export const { machine, scenario } = service({ description: "Hold the limit, starting below its minimum" });

export const limits = machine({
  description: "Hold the limit",
  context: { limit: z.number().min(1).default(0) },
  initial: "holding",
  states: { holding: {} },
}).chart({});
