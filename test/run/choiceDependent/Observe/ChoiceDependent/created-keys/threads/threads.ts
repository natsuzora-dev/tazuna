import { emit, entity, ref, service } from "@natsuzora-dev/tazuna";
import { z } from "zod";

export const Note = entity({
  description: "A note, or a reply to the note replyTo names",
  fields: { id: z.string(), text: z.string(), replyTo: z.string() },
  key: "id",
});

export const { command, machine, event, createEvent, contract, scenario } = service({
  name: "threads",
  description: "Post a note with its reply from each of two clocks at 10:00",
  entities: { Note },
});

export const armed = event({});
export const posted = createEvent({ entity: Note });

export const arm = command({ emits: [armed] }).decide(() => [emit(armed, {})]);

export const post = command({
  input: { id: Note.fields.id, replyId: Note.fields.id, text: Note.fields.text },
  emits: [posted],
}).decide(({ input }) => [
  emit(posted, { id: input.id, text: input.text, replyTo: "" }),
  emit(posted, { id: input.replyId, text: `re: ${input.text}`, replyTo: input.id }),
]);

const clock = (by: string) =>
  machine({
    description: `Post a note with its reply as ${by} at 10:00 once armed`,
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
            input: ({ createKey }) => ({ id: createKey(ref(Note)), replyId: createKey(ref(Note)), text: by }),
            onAccepted: [{ target: "done" }],
            onRejected: [{ target: "done" }],
          },
        },
      },
    },
  });

export const first = clock("first");
export const second = clock("second");

export const threads = contract({ arm });
