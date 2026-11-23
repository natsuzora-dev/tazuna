import { emit, service, singleEntity } from "@natsuzora-dev/tazuna";
import { z } from "zod";

export const Flag = singleEntity({ description: "A flag", fields: { by: z.string().default("") } });

export const { command, machine, event, updateEvent, contract, scenario } = service({
  name: "sameCommand",
  description: "Set the flag by whichever of two sends of one command is answered first",
  entities: { Flag },
});

export const started = event({});
export const flagged = updateEvent({ entity: Flag, writes: ["by"] });

export const start = command({ callers: ["client"], emits: [started] }).decide(() => [emit(started, {})]);

export const ping = command({ callers: ["client", "sameCommand"], emits: [] }).decide(() => []);

export const set = command({ callers: ["client", "sameCommand"], input: { by: z.string() }, emits: [flagged] }).decide(
  ({ input }) => [emit(flagged, { by: input.by })],
);

export const pinger = machine({
  description: "Send ping twice from one state; the send answered first picks who sets the flag",
  receives: { started },
  commands: { first: ping, second: ping, set },
  initial: "idle",
  states: { idle: {}, pinging: {}, byFirst: {}, bySecond: {}, done: {} },
}).chart({
  states: {
    idle: { on: { started: [{ target: "pinging" }] } },
    pinging: {
      sends: {
        first: { onAccepted: [{ target: "byFirst" }] },
        second: { onAccepted: [{ target: "bySecond" }] },
      },
    },
    byFirst: {
      sends: { set: { input: () => ({ by: "first" }), onAccepted: [{ target: "done" }], onRejected: [] } },
    },
    bySecond: {
      sends: { set: { input: () => ({ by: "second" }), onAccepted: [{ target: "done" }], onRejected: [] } },
    },
  },
});

export const sameCommandContract = contract({ start });
