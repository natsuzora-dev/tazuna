import { emit, service, singleEntity } from "@natsuzora-dev/tazuna";
import { z } from "zod";

export const Flag = singleEntity({ description: "A flag", fields: { isOn: z.boolean().default(false) } });

export const { command, query, machine, event, updateEvent, contract, scenario } = service({
  name: "flags",
  description: "Raise and lower a flag for each added task",
  entities: { Flag },
});

export const taskAdded = event({ payload: { id: z.string() } });
export const flagged = updateEvent({ entity: Flag, writes: ["isOn"] });

export const addTask = command({
  input: { taskId: z.string() },
  emits: [taskAdded],
}).decide(({ input }) => [emit(taskAdded, { id: input.taskId })]);

export const raise = command({ emits: [flagged] }).decide(() => [emit(flagged, { isOn: true })]);

export const lower = command({ emits: [flagged] }).decide(() => [emit(flagged, { isOn: false })]);

export const flagger = machine({
  description: "Raise and lower the flag when a task is added",
  receives: { taskAdded },
  commands: { raise, lower },
  initial: "idle",
  states: { idle: {}, flagging: {} },
}).chart({
  states: {
    idle: { on: { taskAdded: [{ target: "flagging" }] } },
    flagging: {
      sends: {
        raise: { onAccepted: [{ target: "idle" }], onRejected: [{ target: "idle" }] },
        lower: { onAccepted: [{ target: "idle" }], onRejected: [{ target: "idle" }] },
      },
    },
  },
});

export const flagText = query({ output: { text: z.string().min(5) } }).resolve(({ records }) => ({
  text: records.Flag.isOn ? "on" : "off",
}));

export const flags = contract({ addTask, flagText });
