import { contract, emit, entity, ref, service } from "@natsuzora-dev/tazuna";
import { z } from "zod";

export const Task = entity({ description: "A task", fields: { id: z.string(), title: z.string() }, key: "id" });

export const { automation, command, machine, query, createEvent, updateEvent } = service({
  description: "Keep the tasks",
  entities: { Task },
});

export const taskAdded = createEvent({ entity: Task });

export const addTask = command({
  input: { taskId: Task.fields.id, title: Task.fields.title },
  emits: [taskAdded],
}).decide(({ input }) => [emit(taskAdded, { id: input.taskId, title: input.title })]);

export const titleChanged = updateEvent({
  entity: Task,
  writes: ["title"],
});

export const trimTitle = command({
  input: { taskId: ref(Task) },
  emits: [titleChanged],
}).decide(({ input, records }) => [
  emit(titleChanged, { id: input.taskId, title: records.Task.get(input.taskId)?.title.trim() ?? "" }),
]);

export const taskCount = query({
  output: { count: z.number() },
}).resolve(({ records }) => ({ count: records.Task.size }));

export const trimFirstTitle = automation({
  receives: { taskAdded },
  commands: { trimTitle },
}).send({
  guard: { first: ({ records }) => records.Task.size === 1 },
  input: ({ payload }) => ({ taskId: payload.id }),
});

export const counter = machine({
  description: "Ask for the number of tasks after each added task",
  receives: { taskAdded },
  queries: { taskCount },
  initial: "idle",
  states: { idle: {}, asking: {} },
}).chart({
  states: {
    idle: { on: { taskAdded: [{ target: "asking" }] } },
    asking: { calls: { taskCount: { onFulfilled: [{ target: "idle" }] } } },
  },
});

export const todo = contract({ addTask, taskCount });
