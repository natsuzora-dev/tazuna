import { emit, service, singleEntity } from "@natsuzora-dev/tazuna";
import { z } from "zod";

export const Alarm = singleEntity({ description: "Who rang the alarm last", fields: { by: z.string().default("") } });

export const { command, machine, event, updateEvent, contract, scenario } = service({
  name: "alarms",
  description: "Ring an alarm at 10:00 from two clocks",
  entities: { Alarm },
});

export const armed = event({});
export const rang = updateEvent({ entity: Alarm, writes: ["by"] });

export const arm = command({ emits: [armed] }).decide(() => [emit(armed, {})]);

export const ring = command({ input: { by: z.string() }, emits: [rang] }).decide(({ input }) => [
  emit(rang, { by: input.by }),
]);

const clock = (by: string) =>
  machine({
    description: `Ring the alarm as ${by} at 10:00 once armed`,
    receives: { armed },
    commands: { ring },
    initial: "idle",
    states: { idle: {}, waiting: { after: ["due"] }, ringing: {}, done: { type: "final" } },
  }).chart({
    states: {
      idle: { on: { armed: [{ target: "waiting" }] } },
      waiting: {
        after: { due: { at: () => Temporal.Instant.from("2026-10-25T01:00:00Z"), onFired: [{ target: "ringing" }] } },
      },
      ringing: {
        sends: { ring: { input: () => ({ by }), onAccepted: [{ target: "done" }], onRejected: [{ target: "done" }] } },
      },
    },
  });

export const first = clock("first");
export const second = clock("second");

export const alarms = contract({ arm });
