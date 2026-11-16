import { contract, emit, entity, ref, service } from "@natsuzora-dev/tazuna";
import { z } from "zod";

export const Entry = entity({ description: "A log entry", fields: { id: z.string(), text: z.string() }, key: "id" });

export const { command, machine, createEvent } = service({
  description: "Log a ring and a chime an hour after the start, the ring as the first entry",
  entities: { Entry },
});

export const entryAdded = createEvent({ entity: Entry });

export const addEntry = command({
  input: { entryId: Entry.fields.id, text: Entry.fields.text },
  emits: [entryAdded],
}).decide(({ input }) => {
  if (input.text === "ring" && input.entryId !== "Entry-1") throw new Error("The ring is not the first entry");
  return [emit(entryAdded, { id: input.entryId, text: input.text })];
});

export const ringer = machine({
  description: "Log a ring an hour after the start, unless the log has one",
  commands: { addEntry },
  initial: "starting",
  states: { starting: {}, waiting: {}, ringing: {}, done: { type: "final" } },
}).chart({
  states: {
    starting: {
      always: [
        { guard: { rang: ({ records }) => records.Entry.some((e) => e.text === "ring") }, target: "done" },
        { target: "waiting" },
      ],
    },
    waiting: { after: { hour: { delay: { hours: 1 }, onFired: [{ target: "ringing" }] } } },
    ringing: {
      sends: {
        addEntry: {
          input: ({ createKey }) => ({ entryId: createKey(ref(Entry), "ring"), text: "ring" }),
          onAccepted: [{ target: "done" }],
          onRejected: [],
        },
      },
    },
  },
});

export const chimer = machine({
  description: "Log a chime an hour after the start, unless the log has one",
  commands: { addEntry },
  initial: "starting",
  states: { starting: {}, waiting: {}, chiming: {}, done: { type: "final" } },
}).chart({
  states: {
    starting: {
      always: [
        { guard: { chimed: ({ records }) => records.Entry.some((e) => e.text === "chime") }, target: "done" },
        { target: "waiting" },
      ],
    },
    waiting: { after: { hour: { delay: { hours: 1 }, onFired: [{ target: "chiming" }] } } },
    chiming: {
      sends: {
        addEntry: {
          input: ({ createKey }) => ({ entryId: createKey(ref(Entry), "chime"), text: "chime" }),
          onAccepted: [{ target: "done" }],
          onRejected: [],
        },
      },
    },
  },
});

export const log = contract({ addEntry });
