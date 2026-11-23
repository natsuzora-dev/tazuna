import { emit, entity, service } from "@natsuzora-dev/tazuna";
import { z } from "zod";

export const Booking = entity({ description: "A day that a task booked", fields: { day: z.string() }, key: "day" });

export const { command, createEvent, contract, scenario } = service({
  name: "calendar",
  description: "Book each day for one task",
  entities: { Booking },
});

export const booked = createEvent({ entity: Booking });

export const reserve = command({
  callers: ["client", "todo"],
  input: { day: z.string() },
  emits: [booked],
  requires: { free: ({ input, records }) => records.Booking.get(input.day) === undefined },
}).decide(({ input }) => [emit(booked, { day: input.day })]);
