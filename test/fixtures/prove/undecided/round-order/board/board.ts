import { emit, service, singleEntity } from "@natsuzora-dev/tazuna";
import { z } from "zod";

export const Board = singleEntity({ description: "Who marked the board last", fields: { by: z.string().default("") } });

export const { command, machine, event, updateEvent } = service({
  name: "board",
  description: "Let two machines mark the board when a ping arrives, each sending its command in one round",
  entities: { Board },
});

export const pinged = event({});

export const marked = updateEvent({ entity: Board, writes: ["by"] });

export const ping = command({ callers: ["client"], emits: [pinged] }).decide(() => [emit(pinged, {})]);

export const mark = command({ callers: ["board"], input: { by: z.string() }, emits: [marked] }).decide(({ input }) => [
  emit(marked, { by: input.by }),
]);

export const first = machine({
  description: "Mark the board as first on each ping",
  receives: { pinged },
  commands: { mark },
  initial: "idle",
  states: { idle: {}, marking: {} },
}).chart({
  states: {
    idle: { on: { pinged: [{ target: "marking" }] } },
    marking: {
      sends: {
        mark: { input: () => ({ by: "first" }), onAccepted: [{ target: "idle" }], onRejected: [{ target: "idle" }] },
      },
    },
  },
});

export const second = machine({
  description: "Mark the board as second on each ping",
  receives: { pinged },
  commands: { mark },
  initial: "idle",
  states: { idle: {}, marking: {} },
}).chart({
  states: {
    idle: { on: { pinged: [{ target: "marking" }] } },
    marking: {
      sends: {
        mark: { input: () => ({ by: "second" }), onAccepted: [{ target: "idle" }], onRejected: [{ target: "idle" }] },
      },
    },
  },
});
