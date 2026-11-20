import { emit, entity, service } from "@natsuzora-dev/tazuna";
import { z } from "zod";

export const Task = entity({ description: "A task", fields: { id: z.string(), title: z.string() }, key: "id" });

export const { automation, command, createEvent } = service({
  name: "worklist",
  description: "Send two commands from one automation, past the types without a written any",
  entities: { Task },
});

export const taskAdded = createEvent({ entity: Task });

export const addTask = command({ input: { id: z.string(), title: z.string() }, emits: [taskAdded] }).decide(
  ({ input }) => [emit(taskAdded, input)],
);

export const addCopy = command({ input: { id: z.string(), title: z.string() }, emits: [taskAdded] }).decide(
  ({ input }) => [emit(taskAdded, input)],
);

export const copyTask = automation({ receives: { taskAdded }, commands: JSON.parse("0") || { addTask, addCopy } }).send(
  {
    input: ({ payload }) => payload,
  },
);
