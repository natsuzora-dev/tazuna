import { externalService } from "@natsuzora-dev/tazuna";
import { z } from "zod";

export const { query, contract } = externalService({ name: "calendar", description: "Return the next business day" });

export const nextBusinessDay = query({ input: { from: z.string() }, output: { day: z.string() }, rejects: [] });
