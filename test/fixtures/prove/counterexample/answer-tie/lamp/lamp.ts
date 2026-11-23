import { emit, service, singleEntity } from "@natsuzora-dev/tazuna";
import { z } from "zod";
import { power } from "../power/contract.ts";

export const Lamp = singleEntity({
  description: "Whether the lamp is lit, and why the power was cut",
  fields: { lit: z.boolean().default(false), cut: z.string().default("") },
});

export const { command, machine, updateEvent } = service({
  name: "lamp",
  description: "Light the lamp once the mains is on, unless the power is cut first",
  entities: { Lamp },
});

export const litChanged = updateEvent({ entity: Lamp, writes: ["lit"] });

export const cutNoted = updateEvent({ entity: Lamp, writes: ["cut"] });

export const light = command({ callers: ["lamp"], emits: [litChanged] }).decide(() => [
  emit(litChanged, { lit: true }),
]);

export const noteCut = command({ callers: ["lamp"], input: { reason: z.string() }, emits: [cutNoted] }).decide(
  ({ input }) => [emit(cutNoted, { cut: input.reason })],
);

export const switcher = machine({
  description: "Ask for the mains, then light the lamp; a cut before that darkens it for good",
  context: { reason: z.string().default("") },
  receives: { cut: power.cut },
  commands: { turnOn: power.turnOn, light, noteCut },
  initial: "asking",
  states: { asking: {}, lighting: {}, lit: {}, dark: {} },
}).chart({
  states: {
    asking: {
      sends: { turnOn: { onAccepted: [{ target: "lighting" }], onRejected: [{ target: "dark" }] } },
      on: { cut: [{ target: "dark", assign: { reason: ({ payload }) => payload.reason } }] },
    },
    lighting: { sends: { light: { onAccepted: [{ target: "lit" }], onRejected: [{ target: "lit" }] } } },
    dark: {
      sends: {
        noteCut: {
          input: ({ context }) => ({ reason: context.reason }),
          onAccepted: [],
          onRejected: [],
        },
      },
    },
  },
});
