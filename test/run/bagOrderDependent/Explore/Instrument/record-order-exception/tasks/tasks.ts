import { bag, emit, entity, ref, service } from "@natsuzora-dev/tazuna";
import { z } from "zod";

export const Task = entity({
  description: "A task, or a subtask of the task parentId",
  fields: { id: z.string(), parentId: ref.self().nullable() },
  key: "id",
});

export const { command, query, createEvent, contract, scenario } = service({
  name: "tasks",
  description: "Keep tasks and subtasks",
  entities: { Task },
});

export const taskAdded = createEvent({ entity: Task });

export const addTask = command({
  input: { taskId: Task.fields.id, parentId: Task.fields.parentId },
  emits: [taskAdded],
}).decide(({ input }) => [emit(taskAdded, { id: input.taskId, parentId: input.parentId })]);

export const subtaskCounts = query({
  output: { counts: bag(z.number()) },
}).resolve(({ records }) => {
  const parents = new Map<string, { subtasks: number }>();
  records.Task.map((task) => {
    if (task.parentId === null) return parents.set(task.id, { subtasks: 0 });
    const parent = parents.get(task.parentId);
    if (parent === undefined) throw new Error(`Task ${task.id} comes before its parent ${task.parentId}`);
    parent.subtasks += 1;
    return parents;
  });
  return { counts: [...parents.values()].map((parent) => parent.subtasks) };
});

export const tasks = contract({ addTask, subtaskCounts });
