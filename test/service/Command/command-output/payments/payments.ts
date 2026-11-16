import { externalService } from "@natsuzora-dev/tazuna";
import { z } from "zod";

export const { command } = externalService({ description: "Process payments" });

export const createCharge = command({
  input: { amount: z.number().int().positive() },
  output: { chargeId: z.string().min(1) },
  emits: [],
  rejects: ["invalid-input", "requires", "unavailable", "reused-id"],
});

export const refundCharge = command({
  input: { chargeId: z.string().min(1) },
  emits: [],
  rejects: ["invalid-input", "requires", "unavailable", "reused-id"],
});
