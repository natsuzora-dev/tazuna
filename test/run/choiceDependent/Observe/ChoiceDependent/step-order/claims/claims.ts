import { emit, entity, ref, service, singleEntity } from "@natsuzora-dev/tazuna";
import { z } from "zod";

export const Task = entity({ description: "A task", fields: { id: z.string() }, key: "id" });

export const Winner = singleEntity({
  description: "The task that claimed last",
  fields: { taskId: z.string().default("") },
});

export const { command, machine, createEvent, updateEvent, contract, scenario } = service({
  description: "Let each added task claim the winner",
  entities: { Task, Winner },
});

export const taskAdded = createEvent({ entity: Task });
export const claimed = updateEvent({ entity: Winner, writes: ["taskId"] });

export const addTasks = command({
  input: { taskIds: z.array(Task.fields.id) },
  emits: [taskAdded],
}).decide(({ input }) => input.taskIds.map((id) => emit(taskAdded, { id })));

export const claim = command({ input: { taskId: ref(Task) }, emits: [claimed] }).decide(({ input }) => [
  emit(claimed, { taskId: input.taskId }),
]);

export const claimer = machine({
  description: "Claim the winner once from the copy of each task",
  commands: { claim },
  initial: "tasks",
  states: {
    tasks: { type: "map", key: { taskId: ref(Task) }, initial: "claiming", states: { claiming: {}, done: {} } },
  },
}).chart({
  states: {
    tasks: { items: ({ records }) => records.Task.map((task) => ({ taskId: task.id })) },
    claiming: { sends: { claim: { input: ({ key }) => key, onAccepted: [{ target: "done" }], onRejected: [] } } },
  },
});

export const claims = contract({ addTasks });
