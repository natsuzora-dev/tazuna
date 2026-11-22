import { emit, entity, parseInstant, ref, service, singleEntity } from "@natsuzora-dev/tazuna";
import { z } from "zod";

export const Note = entity({ description: "A note", fields: { id: z.string() }, key: "id" });
export const Last = singleEntity({ description: "The token set last", fields: { id: Note.fields.id.default("") } });

export const { command, machine, event, updateEvent, contract, scenario } = service({
  name: "tokens",
  description: "One clock clears the token, the other sets a created one, at 10:00",
  entities: { Note, Last },
});

export const armed = event({});
export const moved = updateEvent({ entity: Last, writes: ["id"] });

export const arm = command({ emits: [armed] }).decide(() => [emit(armed, {})]);

export const setLast = command({
  input: { id: Last.fields.id },
  emits: [moved],
}).decide(({ input }) => [emit(moved, { id: input.id })]);

export const first = machine({
  description: "Clear the token at 10:00",
  receives: { armed },
  commands: { setLast },
  initial: "idle",
  states: { idle: {}, waiting: {}, setting: {}, done: { type: "final" } },
}).chart({
  states: {
    idle: { on: { armed: [{ target: "waiting" }] } },
    waiting: {
      after: { due: { at: () => parseInstant("2026-10-25T01:00:00Z"), onFired: [{ target: "setting" }] } },
    },
    setting: {
      sends: {
        setLast: {
          input: () => ({ id: "" }),
          onAccepted: [{ target: "done" }],
          onRejected: [{ target: "done" }],
        },
      },
    },
  },
});

export const second = machine({
  description: "Set a created token at 10:00",
  receives: { armed },
  commands: { setLast },
  initial: "idle",
  states: { idle: {}, waiting: {}, setting: {}, done: { type: "final" } },
}).chart({
  states: {
    idle: { on: { armed: [{ target: "waiting" }] } },
    waiting: {
      after: { due: { at: () => parseInstant("2026-10-25T01:00:00Z"), onFired: [{ target: "setting" }] } },
    },
    setting: {
      sends: {
        setLast: {
          input: ({ createKey }) => ({ id: createKey(ref(Note)) }),
          onAccepted: [{ target: "done" }],
          onRejected: [{ target: "done" }],
        },
      },
    },
  },
});

export const tokens = contract({ arm });
