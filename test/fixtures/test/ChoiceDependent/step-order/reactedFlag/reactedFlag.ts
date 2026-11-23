import { bag, emit, service, singleEntity } from "@natsuzora-dev/tazuna";
import { z } from "zod";

export const Flag = singleEntity({ description: "A flag", fields: { by: z.string().default("") } });

export const { automation, command, event, updateEvent, contract, scenario } = service({
  name: "reactedFlag",
  description: "Set the flag for each added task",
  entities: { Flag },
});

export const taskAdded = event({ payload: { id: z.string() } });
export const flagged = updateEvent({ entity: Flag, writes: ["by"] });

export const addTasks = command({
  callers: ["client"],
  input: { taskIds: bag(z.string()) },
  emits: [taskAdded],
}).decide(({ input }) => [input.taskIds.map((id) => emit(taskAdded, { id }))]);

export const set = command({ callers: ["client", "reactedFlag"], input: { by: z.string() }, emits: [flagged] }).decide(
  ({ input }) => [emit(flagged, { by: input.by })],
);

export const setOnAdd = automation({ receives: { taskAdded }, commands: { set } }).send({
  input: ({ payload }) => ({ by: payload.id }),
});

export const reactedFlagContract = contract({ addTasks });
