import { emit, parseInstant, service, singleEntity } from "@natsuzora-dev/tazuna";
import { z } from "zod";

export const Count = singleEntity({ description: "How many pings were sent", fields: { pings: z.int().default(0) } });

export const { command, machine, updateEvent } = service({
  name: "pinger",
  description: "Ping again on every accepted ping once 10:00 comes, so one deadline starts a chain that never ends",
  entities: { Count },
});

export const pinged = updateEvent({ entity: Count, writes: ["pings"] });

export const ping = command({ callers: ["pinger"], emits: [pinged] }).decide(({ records }) => [
  emit(pinged, { pings: records.Count.pings + 1 }),
]);

export const looper = machine({
  description: "Ping at 10:00, then ping again whenever a ping is accepted",
  commands: { ping },
  initial: "waiting",
  states: { waiting: {}, pinging: {} },
}).chart({
  states: {
    waiting: { after: { due: { at: () => parseInstant("2026-10-25T01:00:00Z"), onFired: [{ target: "pinging" }] } } },
    pinging: { sends: { ping: { onAccepted: [{ target: "pinging", reenter: true }], onRejected: [] } } },
  },
});

export const idle = machine({
  description: "Wait until 10:00 and stop",
  initial: "waiting",
  states: { waiting: {}, stopped: {} },
}).chart({
  states: {
    waiting: { after: { due: { at: () => parseInstant("2026-10-25T01:00:00Z"), onFired: [{ target: "stopped" }] } } },
  },
});
