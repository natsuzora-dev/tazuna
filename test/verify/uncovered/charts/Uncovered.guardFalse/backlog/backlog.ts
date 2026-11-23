import { emit, entity, service } from "@natsuzora-dev/tazuna";
import { z } from "zod";

export const Task = entity({
  description: "A task",
  fields: { id: z.string(), title: z.string(), isDone: z.boolean() },
  key: "id",
});

export const { automation, command, query, machine, createEvent, updateEvent, contract, scenario } = service({
  name: "backlog",
  description: "Keep the tasks",
  entities: { Task },
});

export const taskAdded = createEvent({ entity: Task });

export const addTask = command({
  callers: ["client"],
  input: { taskId: Task.fields.id, title: Task.fields.title },
  emits: [taskAdded],
}).decide(({ input }) => [emit(taskAdded, { id: input.taskId, title: input.title, isDone: false })]);

export const titleWatcher = machine({
  description: "Notice every added task with a title",
  receives: { taskAdded },
  initial: "idle",
  states: { idle: {}, seen: {} },
}).chart({
  states: {
    idle: { on: { taskAdded: [{ guard: { isTitled: ({ payload }) => payload.title !== "" }, target: "seen" }] } },
  },
});

export const backlog = contract({ addTask });
