import { emit, entity, parseInstant, ref, service, singleEntity } from "@natsuzora-dev/tazuna";
import { z } from "zod";

export const Note = entity({ description: "A note", fields: { id: z.string(), text: z.string() }, key: "id" });

export const Count = singleEntity({ description: "Notes posted", fields: { n: z.int().default(0) } });

export const { command, machine, event, createEvent, updateEvent, contract, scenario } = service({
  name: "notes",
  description: "Post a note from each of two clocks at 10:00 and announce it with a label of the form of a key",
  entities: { Note, Count },
});

export const armed = event({});
export const posted = createEvent({ entity: Note });
export const counted = updateEvent({ entity: Count, writes: ["n"] });
export const announced = event({ payload: { noteId: ref(Note), text: Note.fields.text, label: z.string() } });

export const arm = command({ callers: ["client"], emits: [armed] }).decide(() => [emit(armed, {})]);

export const post = command({
  callers: ["client", "notes"],
  input: { id: Note.fields.id, text: Note.fields.text },
  emits: [posted, counted, announced],
}).decide(({ input, records }) => [
  emit(posted, { id: input.id, text: input.text }),
  emit(counted, { n: records.Count.n + 1 }),
  emit(announced, { noteId: input.id, text: input.text, label: "notes/Note-9" }),
]);

export const first = machine({
  description: `Post note a at 10:00 once armed`,
  receives: { armed },
  commands: { post },
  initial: "idle",
  states: { idle: {}, waiting: {}, posting: {}, done: { type: "final" } },
}).chart({
  states: {
    idle: { on: { armed: [{ target: "waiting" }] } },
    waiting: {
      after: { due: { at: () => parseInstant("2026-10-25T01:00:00Z"), onFired: [{ target: "posting" }] } },
    },
    posting: {
      sends: {
        post: {
          input: ({ createKey }) => ({ id: createKey(ref(Note)), text: "a" }),
          onAccepted: [{ target: "done" }],
          onRejected: [{ target: "done" }],
        },
      },
    },
  },
});

export const second = machine({
  description: `Post note b at 10:00 once armed`,
  receives: { armed },
  commands: { post },
  initial: "idle",
  states: { idle: {}, waiting: {}, posting: {}, done: { type: "final" } },
}).chart({
  states: {
    idle: { on: { armed: [{ target: "waiting" }] } },
    waiting: {
      after: { due: { at: () => parseInstant("2026-10-25T01:00:00Z"), onFired: [{ target: "posting" }] } },
    },
    posting: {
      sends: {
        post: {
          input: ({ createKey }) => ({ id: createKey(ref(Note)), text: "b" }),
          onAccepted: [{ target: "done" }],
          onRejected: [{ target: "done" }],
        },
      },
    },
  },
});

export const notes = contract({ arm, announced });
