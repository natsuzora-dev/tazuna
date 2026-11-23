import { emit, entity, ref, service } from "@natsuzora-dev/tazuna";
import { z } from "zod";

export const Task = entity({
  description: "A task",
  fields: { id: z.string(), status: z.enum(["open", "done"]), doneBy: z.string().nullable() },
  key: "id",
  invariants: { doneHasActor: ({ record }) => record.status === "open" || record.doneBy !== null },
});

export const { command, createEvent, updateEvent, bounds } = service({
  name: "todo",
  description: "Keep the tasks",
  entities: { Task },
});

export const taskAdded = createEvent({ entity: Task });

export const statusChanged = updateEvent({ entity: Task, writes: ["status", "doneBy"] });

export const addTask = command({ callers: ["client"], input: { taskId: Task.fields.id }, emits: [taskAdded] }).decide(
  ({ input }) => [emit(taskAdded, { id: input.taskId, status: "open", doneBy: null })],
);

export const completeTask = command({
  callers: ["client"],
  input: { taskId: ref(Task), by: z.string().nullable() },
  emits: [statusChanged],
}).decide(({ input }) => [emit(statusChanged, { id: input.taskId, status: "done", doneBy: input.by })]);

export const reopenTask = command({ callers: ["client"], input: { taskId: ref(Task) }, emits: [statusChanged] }).decide(
  ({ input }) => [emit(statusChanged, { id: input.taskId, status: "open", doneBy: null })],
);

export const todoBounds = bounds({ creates: { Task: 2 } });
