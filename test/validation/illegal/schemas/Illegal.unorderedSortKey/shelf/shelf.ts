import { emit, service, sortedBy } from "@natsuzora-dev/tazuna";
import { z } from "zod";

export const { command, event } = service({ name: "shelf", description: "List items by expiry" });

const mirrored = (instant: Temporal.Instant) => Temporal.Instant.fromEpochMilliseconds(-instant.epochMilliseconds);

const expiry = z.codec(z.iso.datetime({ offset: true }), z.instanceof(Temporal.Instant), {
  decode: (text) => mirrored(Temporal.Instant.from(text)),
  encode: (instant) => mirrored(instant).toString(),
});

export const itemsListed = event({
  payload: { items: sortedBy(z.object({ name: z.string(), expiresAt: expiry }), "expiresAt") },
});

export const listItems = command({ emits: [itemsListed] }).decide(() => [emit(itemsListed, { items: [] })]);
