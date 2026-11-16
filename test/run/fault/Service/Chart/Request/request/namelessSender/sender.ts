import { emit, service } from "@natsuzora-dev/tazuna";
import { z } from "zod";

export const { command, machine, event, scenario } = service({ description: "Send greetings with an empty name" });

export const greeted = event({ payload: { name: z.string() } });

export const greet = command({
  input: { name: z.string().min(1) },
  emits: [greeted],
}).decide(({ input }) => [emit(greeted, { name: input.name })]);

export const greeter = machine({
  description: "Greet once when the service starts",
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
