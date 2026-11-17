import { bag, emit, entity, ref, service } from "@natsuzora-dev/tazuna";
import { z } from "zod";

export const Task = entity({ description: "A task", fields: { id: z.string() }, key: "id" });

export const Mark = entity({ description: "A mark", fields: { id: z.string() }, key: "id" });

export const { automation, command, createEvent, contract, scenario } = service({
  name: "marks",
  description: "Create a mark key for every task whenever a task is added",
  entities: { Task, Mark },
});

export const taskAdded = createEvent({ entity: Task });

export const addTask = command({ input: { taskId: Task.fields.id }, emits: [taskAdded] }).decide(({ input }) => [
  emit(taskAdded, { id: input.taskId }),
]);

export const takeMarks = command({ input: { markIds: bag(Mark.fields.id) }, emits: [] }).decide(() => []);

export const markEveryTask = automation({ receives: { taskAdded }, commands: { takeMarks } }).send({
  input: ({ createKey, records }) => ({ markIds: records.Task.map(() => createKey(ref(Mark))) }),
});

export const marks = contract({ addTask });
