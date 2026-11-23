import { bag, emit, service, singleEntity } from "@natsuzora-dev/tazuna";
import { z } from "zod";

export const Flag = singleEntity({ description: "A flag", fields: { by: z.string().default("") } });

export const { machine, command, event, updateEvent, contract, scenario } = service({
  name: "firstTask",
  description: "Set the flag to the first added task",
  entities: { Flag },
});

export const taskAdded = event({ payload: { id: z.string() } });
export const flagged = updateEvent({ entity: Flag, writes: ["by"] });

export const addTasks = command({
  callers: ["client"],
  input: { taskIds: bag(z.string()) },
  emits: [taskAdded],
}).decide(({ input }) => [input.taskIds.map((id) => emit(taskAdded, { id }))]);

export const set = command({ callers: ["client", "firstTask"], input: { by: z.string() }, emits: [flagged] }).decide(
  ({ input }) => [emit(flagged, { by: input.by })],
);

export const remember = machine({
  description: "Remember the first task added while idle and set the flag to it",
  context: { first: z.string().default("") },
  receives: { taskAdded },
  commands: { set },
  initial: "idle",
  states: { idle: {}, setting: {} },
}).chart({
  states: {
    idle: { on: { taskAdded: [{ target: "setting", assign: { first: ({ payload }) => payload.id } }] } },
    setting: {
      sends: {
        set: {
          input: ({ context }) => ({ by: context.first }),
          onAccepted: [{ target: "idle" }],
          onRejected: [{ target: "idle" }],
        },
      },
    },
  },
});

export const firstTaskContract = contract({ addTasks });
