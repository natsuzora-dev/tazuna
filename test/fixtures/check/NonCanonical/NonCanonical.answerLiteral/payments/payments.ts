import { externalService } from "@natsuzora-dev/tazuna";
import { z } from "zod";

export const { command, contract } = externalService({ name: "payments", description: "Process payments" });

export const createCharge = command({
  callers: [],
  input: { amount: z.int().positive() },
  output: { chargeId: z.string().min(1) },
  emits: [],
  rejects: ["unavailable"],
});

export const payments = contract({ createCharge });
