import { emit, service, singleEntity } from "@natsuzora-dev/tazuna";
import { z } from "zod";
import { mail } from "../mail/contract.ts";

export const Board = singleEntity({
  description: "The board",
  fields: { a: z.boolean().default(false), b: z.boolean().default(false) },
});

export const { command, automation, machine, event, updateEvent } = service({
  name: "board",
  description: "Show the reply that each ping causes, and ask for a notice again when b is shown",
  entities: { Board },
});

export const pinged = event({ payload: { at: z.int() } });
export const aShown = updateEvent({ entity: Board, writes: ["a"] });
export const bShown = updateEvent({ entity: Board, writes: ["b"] });

export const ping = command({ callers: ["client"], input: { at: z.int() }, emits: [pinged] }).decide(({ input }) => [
  emit(pinged, { at: input.at }),
]);

export const showA = command({ callers: ["board"], input: { shown: z.boolean() }, emits: [aShown] }).decide(
  ({ input }) => [emit(aShown, { a: input.shown })],
);

export const showB = command({ callers: ["board"], input: { shown: z.boolean() }, emits: [bShown] }).decide(
  ({ input }) => [emit(bShown, { b: input.shown })],
);

export const replyA = automation({ receives: { pinged }, commands: { showA } }).send({
  input: () => ({ shown: true }),
});

export const replyB = automation({ receives: { pinged }, commands: { showB } }).send({
  input: () => ({ shown: true }),
});

// Both orders of showA and showB end with the same records and out lines and both askers asking. Left asks again when
// b is shown after a, and right otherwise, so the earlier request of the other one still waits, and its answer makes
// left ask once more in one order and right in the other.
export const left = machine({
  description: "Ask for a notice, again when b is shown after a",
  receives: { bShown },
  commands: { notify: mail.notify },
  initial: "asking",
  states: { asking: {}, told: {} },
}).chart({
  states: {
    asking: {
      sends: { notify: { onAccepted: [{ target: "told" }] } },
      on: { bShown: [{ guard: { afterA: ({ records }) => records.Board.a }, target: "asking", reenter: true }] },
    },
    told: { always: [{ target: "asking" }] },
  },
});

export const right = machine({
  description: "Ask for a notice, again when b is shown before a",
  receives: { bShown },
  commands: { notify: mail.notify },
  initial: "asking",
  states: { asking: {}, told: {} },
}).chart({
  states: {
    asking: {
      sends: { notify: { onAccepted: [{ target: "told" }] } },
      on: { bShown: [{ guard: { beforeA: ({ records }) => !records.Board.a }, target: "asking", reenter: true }] },
    },
    told: { always: [{ target: "asking" }] },
  },
});
