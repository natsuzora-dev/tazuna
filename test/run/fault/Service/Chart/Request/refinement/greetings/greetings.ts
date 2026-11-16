import { emit, service } from "@natsuzora-dev/tazuna";
import { z } from "zod";

export const { command, machine, event, scenario } = service({ description: "Greet when the service starts" });

export const greeted = event({ payload: { name: z.string() } });

export const greet = command({
  input: {
    name: z.string().refine((name) => {
      if (name === "") throw new Error("a greeting needs a name");
      return true;
    }),
  },
  emits: [greeted],
}).decide(({ input }) => [emit(greeted, { name: input.name })]);

export const greeter = machine({
  description: "Greet once with an empty name",
  commands: { greet },
  initial: "greeting",
  states: { greeting: {}, done: { type: "final" } },
}).chart({
  states: {
    greeting: {
      sends: {
        greet: { input: () => ({ name: "" }), onAccepted: [{ target: "done" }] },
      },
    },
  },
});
