import { emit, service, singleEntity } from "@natsuzora-dev/tazuna";
import { z } from "zod";

export const Lock = singleEntity({
  description: "The lock of the door",
  fields: { locked: z.boolean().default(false) },
});

export const { command, machine, updateEvent } = service({
  name: "door",
  description: "Ring while the door is unlocked",
  entities: { Lock },
});

export const lockChanged = updateEvent({ entity: Lock, writes: ["locked"] });

export const setLock = command({ input: { locked: z.boolean() }, emits: [lockChanged] }).decide(({ input }) => [
  emit(lockChanged, { locked: input.locked }),
]);

export const alarm = machine({
  description: "Ring each second while the door is unlocked, counting the rings",
  context: { rings: z.int().default(0) },
  receives: { lockChanged },
  initial: "idle",
  states: { idle: {}, ringing: {} },
  invariants: {
    countsOnlyWhileRinging: ({ context, active }) => active.ringing || context.rings === 0,
  },
}).chart({
  states: {
    idle: {
      entry: { assign: { rings: () => 0 } },
      on: { lockChanged: [{ guard: { unlocked: ({ payload }) => payload.locked === false }, target: "ringing" }] },
    },
    ringing: {
      entry: { assign: { rings: ({ context }) => context.rings + 1 } },
      always: [{ guard: { locked: ({ records }) => records.Lock.locked }, target: "idle" }],
      after: { ring: { delay: 1000, onFired: [{ target: "ringing", reenter: true }] } },
    },
  },
});
