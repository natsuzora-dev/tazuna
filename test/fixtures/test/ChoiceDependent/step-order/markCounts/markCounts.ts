import { emit, entity, service } from "@natsuzora-dev/tazuna";
import { z } from "zod";

// Each task has a mark in slot a and one in slot b: the task and the slot are the key.
export const Mark = entity({
  description: "A mark",
  fields: { taskId: z.string(), slot: z.enum(["a", "b"]), count: z.int() },
  key: ["taskId", "slot"],
});

export const { automation, command, event, createEvent, contract, scenario } = service({
  name: "markCounts",
  description: "Mark each added task twice",
  entities: { Mark },
});

export const taskAdded = event({ payload: { id: z.string() } });
export const marked = createEvent({ entity: Mark });

export const addTask = command({ callers: ["client"], input: { taskId: z.string() }, emits: [taskAdded] }).decide(
  ({ input }) => [emit(taskAdded, { id: input.taskId })],
);

export const markA = command({
  callers: ["client", "markCounts"],
  input: { taskId: z.string() },
  emits: [marked],
}).decide(({ input, records }) =>
  records.Mark.get({ taskId: input.taskId, slot: "a" }) === undefined
    ? [emit(marked, { taskId: input.taskId, slot: "a", count: 0 })]
    : [],
);

export const markB = command({
  callers: ["client", "markCounts"],
  input: { taskId: z.string() },
  emits: [marked],
}).decide(({ input, records }) =>
  records.Mark.get({ taskId: input.taskId, slot: "b" }) === undefined
    ? [emit(marked, { taskId: input.taskId, slot: "b", count: records.Mark.size })]
    : [],
);

export const markWithA = automation({
  receives: { taskAdded },
  commands: { markA },
}).send({ input: ({ payload }) => ({ taskId: payload.id }) });

export const markWithB = automation({
  receives: { taskAdded },
  commands: { markB },
}).send({ input: ({ payload }) => ({ taskId: payload.id }) });

export const markCounts = contract({ addTask });
