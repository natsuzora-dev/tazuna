import { service } from "@natsuzora-dev/tazuna";
import { z } from "zod";

export const { command, contract } = service({ name: "ledger", description: "Keep the amounts" });

const cents = z.codec(z.string(), z.number(), { decode: (s) => Number(s), encode: (n) => String(n) });

export const record = command({
  input: { byItem: z.record(z.string(), cents), range: z.tuple([cents, cents]) },
  emits: [],
}).decide(() => []);
