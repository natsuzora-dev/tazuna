import { constants, duration, emit, entity, service } from "@natsuzora-dev/tazuna";
import { z } from "zod";

export const todoConstants = constants({
  service: "todo",
  schema: z.object({ titleLengthMax: z.int(), reminderOffsets: z.array(duration), defaultLabel: z.string() }),
  values: { titleLengthMax: 80, reminderOffsets: [600_000, 3_600_000], defaultLabel: "inbox" },
});

export const Task = entity({
  description: "A task",
  fields: { id: z.string(), title: z.string().max(todoConstants.titleLengthMax), label: z.string() },
  key: "id",
});

export const { command, createEvent, contract } = service({
  name: "todo",
  description: "Keep the tasks",
  entities: { Task },
});

export const taskAdded = createEvent({ entity: Task });

export const addTask = command({
  input: { taskId: Task.fields.id, title: Task.fields.title },
  emits: [taskAdded],
}).decide(({ input }) => [
  emit(taskAdded, { id: input.taskId, title: input.title, label: todoConstants.defaultLabel }),
]);

export const titleLengthMax = 80;
export const reminderOffsets = [{ minutes: 10 }, { hours: 1 }];
export const defaultLabel = "inbox";

export const addLabeledTask = command({
  input: { taskId: Task.fields.id, title: z.string().max(titleLengthMax) },
  emits: [taskAdded],
}).decide(({ input }) => [emit(taskAdded, { id: input.taskId, title: input.title, label: defaultLabel })]);

export const todo = contract({ addTask, addLabeledTask, todoConstants });
