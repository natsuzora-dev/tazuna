import { bag, emit, entity, ref, service } from "@natsuzora-dev/tazuna";
import { z } from "zod";

export const Note = entity({
  description: "A note, or a reply to the note replyTo names",
  fields: { id: z.string(), text: z.string(), replyTo: ref.self().nullable() },
  key: "id",
});

export const { automation, command, query, event, createEvent, contract, scenario } = service({
  name: "notes",
  description: "Post a note and a reply to it, and list the notes",
  entities: { Note },
});

export const started = event({});
export const posted = createEvent({ entity: Note });
export const replied = createEvent({ entity: Note });

export const start = command({ callers: ["client"], emits: [started] }).decide(() => [emit(started, {})]);

export const post = command({
  callers: ["client", "notes"],
  input: { id: Note.fields.id, text: Note.fields.text, replyTo: Note.fields.replyTo },
  emits: [posted],
}).decide(({ input }) => [emit(posted, input)]);

export const postFirst = automation({
  receives: { started },
  commands: { post },
}).send({ input: ({ createKey }) => ({ id: createKey(ref(Note)), text: "first", replyTo: null }) });

export const reply = command({
  callers: ["client", "notes"],
  input: { id: Note.fields.id, replyTo: Note.fields.replyTo },
  emits: [replied],
}).decide(({ input }) => [emit(replied, { id: input.id, text: "reply", replyTo: input.replyTo })]);

export const replyToPosted = automation({
  receives: { posted },
  commands: { reply },
}).send({ input: ({ payload, createKey }) => ({ id: createKey(ref(Note)), replyTo: payload.id }) });

export const thread = query({ callers: ["client"], output: { notes: bag(z.object(Note.fields)) } }).resolve(
  ({ records }) => ({
    notes: records.Note,
  }),
);

export const notes = contract({ start, thread });
