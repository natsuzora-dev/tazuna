import { contract, emit, entity, ref, service } from "@natsuzora-dev/tazuna";
import { z } from "zod";

export const Entry = entity({ description: "A log entry", fields: { id: z.string(), text: z.string() }, key: "id" });

export const { command, event, machine, createEvent } = service({
  description: "Log a ring and a chime an hour after the start",
  entities: { Entry },
});

export const entryAdded = createEvent({ entity: Entry });

export const entryLogged = event({ payload: { entryId: Entry.fields.id, text: Entry.fields.text } });

export const addEntry = command({
  input: { entryId: Entry.fields.id, text: Entry.fields.text },
  emits: [entryAdded, entryLogged],
}).decide(({ input }) => [
  emit(entryAdded, { id: input.entryId, text: input.text }),
  emit(entryLogged, { entryId: input.entryId, text: input.text }),
]);

export const ringer = machine({
  description: "Log a ring an hour after the start",
  commands: { addEntry },
  initial: "waiting",
  states: { waiting: {}, ringing: {}, done: { type: "final" } },
}).chart({
  states: {
    waiting: { after: { hour: { delay: { hours: 1 }, onFired: [{ target: "ringing" }] } } },
    ringing: {
      sends: {
        addEntry: {
          input: ({ createKey }) => ({ entryId: createKey(ref(Entry)), text: "ring" }),
          onAccepted: [{ target: "done" }],
          onRejected: [],
        },
      },
    },
  },
});

export const chimer = machine({
  description: "Log a chime an hour after the start",
  commands: { addEntry },
  initial: "waiting",
  states: { waiting: {}, chiming: {}, done: { type: "final" } },
}).chart({
  states: {
    waiting: { after: { hour: { delay: { hours: 1 }, onFired: [{ target: "chiming" }] } } },
    chiming: {
      sends: {
        addEntry: {
          input: ({ createKey }) => ({ entryId: createKey(ref(Entry)), text: "chime" }),
          onAccepted: [{ target: "done" }],
          onRejected: [],
        },
      },
    },
  },
});

export const log = contract({ addEntry, entryLogged });
