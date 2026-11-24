import { addDays, date, emit, entity, service, singleEntity } from "@natsuzora-dev/tazuna";
import { z } from "zod";
import { sensor } from "../sensor/contract.ts";

export const Flag = singleEntity({
  description: "Whether a set reading arrived",
  fields: { on: z.boolean().default(false) },
});

export const Note = entity({
  description: "A note",
  fields: { id: z.string(), due: date },
  key: "id",
});

export const { command, automation, updateEvent, createEvent, bounds } = service({
  name: "board",
  description: "React to readings",
  entities: { Flag, Note },
});

export const flagChanged = updateEvent({ entity: Flag, writes: ["on"] });
export const noted = createEvent({ entity: Note });

export const apply = command({
  callers: ["board"],
  input: { kind: z.enum(["set", "check"]), late: z.boolean() },
  emits: [flagChanged, noted],
}).decide(({ input }) => (input.kind === "set" ? [emit(flagChanged, { on: true })] : []));

export const boardBounds = bounds({ creates: { Note: 1 } });

// addDays past the last date throws, so the react halts on a check reading only after a set reading, in one order.
export const applyReading = automation({ receives: { read: sensor.read }, commands: { apply } }).send({
  input: ({ payload, records }) => {
    const n = records.Note.get("x");
    return {
      kind: payload.kind,
      late: payload.kind === "check" && records.Flag.on && n !== undefined && addDays(n.due, 3_000_000) > n.due,
    };
  },
});
