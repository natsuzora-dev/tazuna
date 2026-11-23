import { emit, entity, service, singleEntity } from "@natsuzora-dev/tazuna";
import { z } from "zod";

export const Guest = entity({ description: "A guest at the door", fields: { id: z.string() }, key: "id" });

export const Hall = singleEntity({ description: "The guest greeted last", fields: { last: z.string().default("") } });

export const { command, automation, event, updateEvent, bounds } = service({
  name: "bell",
  description: "Call every guest at once, and greet each guest called",
  entities: { Guest, Hall },
});

export const called = event({ payload: { guest: z.string() } });

export const greeted = updateEvent({ entity: Hall, writes: ["last"] });

export const callAll = command({ callers: ["client"], emits: [called] }).decide(({ records }) => [
  records.Guest.map((g) => emit(called, { guest: g.id })),
]);

export const greet = command({ callers: ["bell"], input: { guest: z.string() }, emits: [greeted] }).decide(
  ({ input }) => [emit(greeted, { last: input.guest })],
);

export const greetCalled = automation({ receives: { called }, commands: { greet } }).send({
  input: ({ payload }) => ({ guest: payload.guest }),
});

export const bellBounds = bounds({ creates: { Guest: 2 } });
