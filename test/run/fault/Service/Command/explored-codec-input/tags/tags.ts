import { service } from "@natsuzora-dev/tazuna";
import { z } from "zod";

export const { command, contract, scenario } = service({ name: "tags", description: "Keep the tags" });

const upper = z.codec(z.string(), z.string(), { decode: (s) => s.toUpperCase(), encode: (s) => s.toLowerCase() });

export const tag = command({ input: { name: upper }, emits: [] }).decide(({ input }) => {
  throw new Error(`tagged ${input.name}`);
});

export const tags = contract({ tag });
