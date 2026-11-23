import { emit, entity, service } from "@natsuzora-dev/tazuna";
import { z } from "zod";

export const Task = entity({ description: "A task of the user", fields: { id: z.string() }, key: "id" });

export const { command, query, createEvent, contract } = service({
  name: "todo",
  description: "Keep tasks",
  entities: { Task },
});

export const taskAdded = createEvent({ entity: Task });

export const addTask = command({ callers: ["client"], input: { taskId: Task.fields.id }, emits: [taskAdded] }).decide(
  ({ input }) => [emit(taskAdded, { id: input.taskId })],
);

export const note = command({ callers: ["client", "screens"], input: { count: z.int() }, emits: [] }).decide(() => []);

export const taskCount = query({ callers: ["client", "screens"], output: { count: z.int() } }).resolve(
  ({ records }) => ({
    count: records.Task.size,
  }),
);
