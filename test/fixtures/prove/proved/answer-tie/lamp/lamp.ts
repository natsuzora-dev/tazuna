import { emit, service, singleEntity } from "@natsuzora-dev/tazuna";
import { z } from "zod";
import { power } from "../power/contract.ts";

export const Lamp = singleEntity({
  description: "Whether the lamp is lit, and whether the power was cut",
  fields: { lit: z.boolean().default(false), cut: z.boolean().default(false) },
});

export const { command, machine, automation, updateEvent } = service({
  name: "lamp",
  description: "Light the lamp once the mains is on, and note a power cut apart",
  entities: { Lamp },
});

export const litChanged = updateEvent({ entity: Lamp, writes: ["lit"] });

export const cutNoted = updateEvent({ entity: Lamp, writes: ["cut"] });

export const light = command({ callers: ["lamp"], emits: [litChanged] }).decide(() => [
  emit(litChanged, { lit: true }),
]);

export const noteCut = command({ callers: ["lamp"], emits: [cutNoted] }).decide(() => [emit(cutNoted, { cut: true })]);

export const noteCuts = automation({ receives: { cut: power.cut }, commands: { noteCut } }).send({});

export const switcher = machine({
  description: "Ask for the mains, then light the lamp",
  commands: { turnOn: power.turnOn, light },
  initial: "asking",
  states: { asking: {}, lighting: {}, dark: {} },
}).chart({
  states: {
    asking: { sends: { turnOn: { onAccepted: [{ target: "lighting" }], onRejected: [{ target: "dark" }] } } },
    lighting: { sends: { light: { onAccepted: [{ target: "dark" }], onRejected: [{ target: "dark" }] } } },
  },
});
