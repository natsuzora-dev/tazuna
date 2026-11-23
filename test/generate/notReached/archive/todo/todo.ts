import { emit, entity, ref, service } from "@natsuzora-dev/tazuna";
import { z } from "zod";

export const Task = entity({
  description: "A task that is archived once it was done and reopened",
  fields: { id: z.string(), status: z.enum(["open", "done", "reopened", "archived"]) },
  key: "id",
});

export const { command, createEvent, updateEvent, bounds } = service({
  name: "todo",
  description: "Keep the tasks",
  entities: { Task },
});

export const taskAdded = createEvent({ entity: Task });
export const statusChanged = updateEvent({ entity: Task, writes: ["status"] });

export const addTask = command({ callers: ["client"], input: { taskId: Task.fields.id }, emits: [taskAdded] }).decide(
  ({ input }) => [emit(taskAdded, { id: input.taskId, status: "open" })],
);

export const completeTask = command({
  callers: ["client"],
  input: { taskId: ref(Task) },
  emits: [statusChanged],
  requires: { open: ({ input, records }) => records.Task.get(input.taskId)?.status === "open" },
}).decide(({ input }) => [emit(statusChanged, { id: input.taskId, status: "done" })]);

export const reopenTask = command({
  callers: ["client"],
  input: { taskId: ref(Task) },
  emits: [statusChanged],
  requires: { done: ({ input, records }) => records.Task.get(input.taskId)?.status === "done" },
}).decide(({ input }) => [emit(statusChanged, { id: input.taskId, status: "reopened" })]);

export const archiveTask = command({
  callers: ["client"],
  input: { taskId: ref(Task) },
  emits: [statusChanged],
  requires: { reopened: ({ input, records }) => records.Task.get(input.taskId)?.status === "reopened" },
}).decide(({ input }) => [emit(statusChanged, { id: input.taskId, status: "archived" })]);

export const todoBounds = bounds({ creates: { Task: 1 } });
