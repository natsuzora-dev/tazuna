import { emit, entity, service } from "@natsuzora-dev/tazuna";
import { z } from "zod";

export const Guest = entity({ description: "A guest at the door", fields: { id: z.string() }, key: "id" });

export const { command, machine, event, bounds } = service({
  name: "bell",
  description: "Call every guest at once, and greet the guest called last",
  entities: { Guest },
});

export const called = event({ payload: { guest: z.string() } });

export const callAll = command({ callers: ["client"], emits: [called] }).decide(({ records }) => [
  records.Guest.map((g) => emit(called, { guest: g.id })),
]);

export const greeter = machine({
  description: "Remember the guest called last, which depends on the order of one group's events",
  context: { last: z.string().default("") },
  receives: { called },
  initial: "idle",
  states: { idle: {} },
}).chart({
  states: {
    idle: { on: { called: [{ target: "idle", reenter: true, assign: { last: ({ payload }) => payload.guest } }] } },
  },
});

export const bellBounds = bounds({ creates: { Guest: 2 } });
