import { service } from "@natsuzora-dev/tazuna";
import { z } from "zod";

export const { command, contract, scenario } = service({ name: "club", description: "Keep the notes and invites" });

export const note = command({ input: { text: z.string() }, emits: [] }).decide(() => []);

export const invite = command({ input: { email: z.string().email() }, emits: [] }).decide(({ input }) => {
  throw new Error(`invited ${input.email}`);
});

export const club = contract({ note, invite });
