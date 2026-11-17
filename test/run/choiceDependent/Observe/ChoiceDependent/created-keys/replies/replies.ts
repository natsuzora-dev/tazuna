import { emit, entity, ref, service, singleEntity } from "@natsuzora-dev/tazuna";
import { z } from "zod";

export const Note = entity({
  description: "A note, or a reply to the note replyTo names",
  fields: { id: z.string(), text: z.string(), replyTo: z.string() },
  key: "id",
});

export const Last = singleEntity({ description: "The note posted last", fields: { id: z.string().default("") } });

export const { command, machine, event, createEvent, updateEvent, contract, scenario } = service({
  name: "replies",
  description: "Post a note from each of two clocks at 10:00, replying to the note posted before it",
  entities: { Note, Last },
});

export const armed = event({});
export const posted = createEvent({ entity: Note });
export const moved = updateEvent({ entity: Last, writes: ["id"] });

export const arm = command({ emits: [armed] }).decide(() => [emit(armed, {})]);

export const post = command({
  input: { id: Note.fields.id, text: Note.fields.text },
  emits: [posted, moved],
}).decide(({ input, records }) => [
  emit(posted, { id: input.id, text: input.text, replyTo: records.Last.id }),
  emit(moved, { id: input.id }),
]);

const clock = (by: string) =>
  machine({
    description: `Post a note as ${by} at 10:00 once armed`,
    receives: { armed },
    commands: { post },
    initial: "idle",
    states: { idle: {}, waiting: {}, posting: {}, done: { type: "final" } },
  }).chart({
    states: {
      idle: { on: { armed: [{ target: "waiting" }] } },
      waiting: {
        after: { due: { at: () => Temporal.Instant.from("2026-10-25T01:00:00Z"), onFired: [{ target: "posting" }] } },
      },
      posting: {
        sends: {
          post: {
            input: ({ createKey }) => ({ id: createKey(ref(Note)), text: by }),
            onAccepted: [{ target: "done" }],
            onRejected: [{ target: "done" }],
          },
        },
      },
    },
  });

export const first = clock("first");
export const second = clock("second");

export const replies = contract({ arm });
