import { emit, entity, ref, service } from "@natsuzora-dev/tazuna";
import { z } from "zod";

export const Mark = entity({ description: "A mark", fields: { id: z.string(), count: z.int() }, key: "id" });

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

export const markA = command({ callers: ["client", "markCounts"], input: { id: z.string() }, emits: [marked] }).decide(
  ({ input, records }) => (records.Mark.get(input.id) === undefined ? [emit(marked, { id: input.id, count: 0 })] : []),
);

export const markB = command({ callers: ["client", "markCounts"], input: { id: z.string() }, emits: [marked] }).decide(
  ({ input, records }) =>
    records.Mark.get(input.id) === undefined ? [emit(marked, { id: input.id, count: records.Mark.size })] : [],
);

export const markWithA = automation({
  receives: { taskAdded },
  commands: { markA },
}).send({ input: ({ createKey }) => ({ id: createKey(ref(Mark)) }) });

export const markWithB = automation({
  receives: { taskAdded },
  commands: { markB },
}).send({ input: ({ createKey }) => ({ id: createKey(ref(Mark)) }) });

export const markCounts = contract({ addTask });
