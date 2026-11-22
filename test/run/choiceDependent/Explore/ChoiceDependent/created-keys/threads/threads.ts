import { emit, entity, parseInstant, ref, service, singleEntity } from "@natsuzora-dev/tazuna";
import { z } from "zod";

export const Note = entity({
  description: "A note, or a reply to the note replyTo names",
  fields: { id: z.string(), text: z.string(), replyTo: ref.self().nullable() },
  key: "id",
});

export const Count = singleEntity({
  description: "How many notes were posted",
  fields: { notes: z.number().default(0) },
});

export const { command, machine, event, createEvent, updateEvent, contract, scenario } = service({
  name: "threads",
  description: "Post a note and a reply to it from each of two clocks at 10:00",
  entities: { Note, Count },
});

export const armed = event({});
export const posted = createEvent({ entity: Note });
export const counted = updateEvent({ entity: Count, writes: ["notes"] });

export const arm = command({ emits: [armed] }).decide(() => [emit(armed, {})]);

export const postThread = command({
  input: { id: Note.fields.id, replyId: Note.fields.id, text: Note.fields.text },
  emits: [posted, counted],
}).decide(({ input, records }) => [
  emit(posted, { id: input.id, text: input.text, replyTo: null }),
  emit(posted, { id: input.replyId, text: `re: ${input.text}`, replyTo: input.id }),
  emit(counted, { notes: records.Count.notes + 2 }),
]);

export const first = machine({
  description: `Post a note and a reply to it as first at 10:00 once armed`,
  receives: { armed },
  commands: { postThread },
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
        postThread: {
          input: ({ createKey }) => ({ id: createKey(ref(Note)), replyId: createKey(ref(Note)), text: "first" }),
          onAccepted: [{ target: "done" }],
          onRejected: [{ target: "done" }],
        },
      },
    },
  },
});

export const second = machine({
  description: `Post a note and a reply to it as second at 10:00 once armed`,
  receives: { armed },
  commands: { postThread },
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
        postThread: {
          input: ({ createKey }) => ({ id: createKey(ref(Note)), replyId: createKey(ref(Note)), text: "second" }),
          onAccepted: [{ target: "done" }],
          onRejected: [{ target: "done" }],
        },
      },
    },
  },
});

export const threads = contract({ arm });
