import { emit, entity, service } from "@natsuzora-dev/tazuna";
import { z } from "zod";

export const Task = entity({ description: "A task of the user", fields: { id: z.string() }, key: "id" });

export const { automation, command, event, createEvent, contract, scenario } = service({
  name: "todo",
  description: "Keep tasks",
  entities: { Task },
});

export const taskAdded = createEvent({ entity: Task });
export const counted = event({ payload: { count: z.int() } });

export const addTask = command({ callers: ["client"], input: { taskId: Task.fields.id }, emits: [taskAdded] }).decide(
  ({ input }) => [emit(taskAdded, { id: input.taskId })],
);

export const tellCount = command({ callers: ["client", "todo"], input: { count: z.int() }, emits: [counted] }).decide(
  ({ input }) => [emit(counted, { count: input.count })],
);

export const countAdded = automation({
  receives: { taskAdded },
  commands: { tellCount },
}).send({ input: ({ records }) => ({ count: records.Task.size }) });
