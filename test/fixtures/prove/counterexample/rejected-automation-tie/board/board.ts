import { emit, service, singleEntity } from "@natsuzora-dev/tazuna";
import { z } from "zod";
import { sensor } from "../sensor/contract.ts";

export const Flag = singleEntity({
  description: "Whether a set reading arrived",
  fields: { on: z.boolean().default(false) },
});

export const { command, automation, updateEvent } = service({
  name: "board",
  description: "React to readings",
  entities: { Flag },
});

export const flagChanged = updateEvent({ entity: Flag, writes: ["on"] });

// A check reading is rejected only after a set reading, in one order, which reports rejectedAutomationCommand.
export const apply = command({
  callers: ["board"],
  input: { kind: z.enum(["set", "check"]) },
  emits: [flagChanged],
  requires: { offOrSet: ({ input, records }) => input.kind === "set" || !records.Flag.on },
}).decide(({ input }) => (input.kind === "set" ? [emit(flagChanged, { on: true })] : []));

export const applyReading = automation({ receives: { read: sensor.read }, commands: { apply } }).send({
  input: ({ payload }) => ({ kind: payload.kind }),
});
