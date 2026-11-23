import { externalService } from "@natsuzora-dev/tazuna";
import { z } from "zod";

export const { command, contract } = externalService({ name: "payments", description: "Process payments" });

export const createCharge = command({
  callers: ["shop"],
  input: { amount: z.int().positive() },
  output: { chargeId: z.string().min(1) },
  emits: [],
  rejects: ["invalid-input", "requires", "unavailable", "reused-id"],
});

export const refundCharge = command({
  callers: ["shop"],
  input: { chargeId: z.string().min(1) },
  emits: [],
  rejects: ["invalid-input", "requires", "unavailable", "reused-id"],
});
