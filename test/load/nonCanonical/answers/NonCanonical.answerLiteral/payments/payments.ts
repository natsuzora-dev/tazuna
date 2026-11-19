import { externalService } from "@natsuzora-dev/tazuna";
import { z } from "zod";

export const { command, contract } = externalService({ name: "payments", description: "Process payments" });

export const createCharge = command({
  input: { amount: z.number().int().positive() },
  output: { chargeId: z.string().min(1) },
  emits: [],
  rejects: ["unavailable"],
});

export const payments = contract({ createCharge });
