import { emit, entity, service } from "@natsuzora-dev/tazuna";
import { z } from "zod";

export const Task = entity({
  description: "A task",
  fields: { id: z.string(), title: z.string(), isDone: z.boolean() },
  key: "id",
});

export const { command, machine, createEvent, updateEvent, contract, scenario } = service({
  name: "backlog",
  description: "Keep the tasks",
  entities: { Task },
});

export const taskAdded = createEvent({ entity: Task });

export const addTask = command({
  input: { taskId: Task.fields.id, title: Task.fields.title },
  emits: [taskAdded],
}).decide(({ input }) => [emit(taskAdded, { id: input.taskId, title: input.title, isDone: false })]);

export const taskCompleted = updateEvent({ entity: Task, writes: ["isDone"] });

export const completeTask = command({
  input: { title: Task.fields.title },
  emits: [taskCompleted],
  binds: { task: ({ input, records }) => records.Task.filter((t) => t.title === input.title).only() },
  requires: { notDone: ({ bound }) => !bound.task.isDone },
}).decide(({ bound }) => [emit(taskCompleted, { id: bound.task.id, isDone: true })]);

export const progress = machine({
  description: "Follow the progress of tasks",
  receives: { taskAdded, taskCompleted },
  initial: "empty",
  states: { empty: {}, busy: {}, done: {}, archived: {} },
}).chart({
  states: {
    empty: { on: { taskAdded: [{ target: "busy" }] } },
    busy: {
      on: {
        taskCompleted: [{ guard: { allDone: ({ records }) => records.Task.every((t) => t.isDone) }, target: "done" }],
      },
    },
    done: { on: { taskAdded: [{ target: "busy" }] } },
  },
});

export const titleWatcher = machine({
  description: "Notice every added task; the first transition takes titles that contain milk",
  receives: { taskAdded },
  initial: "idle",
  states: { idle: {}, seen: {} },
}).chart({
  states: {
    idle: {
      on: {
        taskAdded: [
          {
            guard: {
              isTitled: ({ payload }) => payload.title !== "",
              isMilk: ({ payload }) => payload.title.includes("milk"),
            },
            target: "seen",
          },
          { target: "seen" },
        ],
      },
    },
    seen: { on: { taskAdded: [{ target: "idle" }] } },
  },
});

export const backlog = contract({ addTask, completeTask });
