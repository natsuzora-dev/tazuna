import { emit, entity, service } from "@natsuzora-dev/tazuna";
import { z } from "zod";

export const Reading = entity({
  description: "A reading of a meter",
  fields: { id: z.string(), value: z.number() },
  key: "id",
  invariants: { notBetweenZeroAndOne: ({ record }) => record.value <= 0 || record.value >= 1 },
});

export const { command, createEvent, bounds } = service({
  name: "meter",
  description: "Keep the readings",
  entities: { Reading },
});

export const readingTaken = createEvent({ entity: Reading });

export const takeReading = command({
  input: { readingId: Reading.fields.id, value: z.number() },
  emits: [readingTaken],
}).decide(({ input }) => [emit(readingTaken, { id: input.readingId, value: input.value })]);

export const meterBounds = bounds({ creates: { Reading: 2 } });
