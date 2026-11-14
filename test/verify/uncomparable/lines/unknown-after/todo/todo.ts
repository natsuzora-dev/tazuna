import { datetime, emit, entity, ref, service } from "@natsuzora-dev/tazuna";
import { z } from "zod";
import { calendar } from "../calendar/contract.ts";

export const Task = entity({
  description: "A task",
  fields: { id: z.string(), title: z.string(), dueAt: datetime.nullable() },
  key: "id",
});

export const { command, machine, event, createEvent } = service({ description: "Keep the tasks", entities: { Task } });

export const taskAddedRecorded = createEvent({ entity: Task });

export const taskAdded = event({ payload: { taskId: ref(Task) } });

export const taskCountChanged = event({ payload: { count: z.int() } });

export const addTask = command({
  input: { taskId: Task.fields.id, title: Task.fields.title },
  emits: [taskAddedRecorded, taskAdded, taskCountChanged],
}).decide(({ input, records }) => [
  emit(taskAddedRecorded, { id: input.taskId, title: input.title, dueAt: null }),
  emit(taskAdded, { taskId: input.taskId }),
  emit(taskCountChanged, { count: records.Task.size + 1 }),
]);

export const planner = machine({
  description: "Ask for the next day of the latest added task",
  receives: { taskAddedRecorded },
  queries: { nextDay: calendar.nextDay },
  initial: "idle",
  states: { idle: {}, asking: {} },
}).chart({
  on: { taskAddedRecorded: [{ target: "asking" }] },
  states: {
    asking: {
      calls: {
        nextDay: {
          input: ({ now }) => ({ from: now }),
          onFulfilled: [{ target: "idle" }],
          onRejected: [{ target: "idle" }],
        },
      },
    },
  },
});
