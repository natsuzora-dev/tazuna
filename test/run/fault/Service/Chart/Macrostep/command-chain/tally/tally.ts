import { emit, service, singleEntity } from "@natsuzora-dev/tazuna";
import { z } from "zod";

export const Counter = singleEntity({ description: "A counter", fields: { value: z.number().default(0) } });

export const { command, machine, updateEvent, scenario } = service({
  description: "Keep a tally",
  entities: { Counter },
});

export const counted = updateEvent({ entity: Counter, writes: ["value"] });

export const count = command({
  emits: [counted],
}).decide(({ records }) => [emit(counted, { value: records.Counter.value + 1 })]);

export const counter = machine({
  description: "Count on every count, going back and forth between two states while the value is below three",
  receives: { counted },
  commands: { count },
  initial: "ping",
  states: { ping: {}, pong: {} },
}).chart({
  states: {
    ping: {
      on: { counted: [{ guard: { belowThree: ({ records }) => records.Counter.value < 3 }, target: "pong" }] },
      sends: { count: { onAccepted: [], onRejected: [] } },
    },
    pong: {
      on: { counted: [{ guard: { belowThree: ({ records }) => records.Counter.value < 3 }, target: "ping" }] },
      sends: { count: { onAccepted: [], onRejected: [] } },
    },
  },
});
