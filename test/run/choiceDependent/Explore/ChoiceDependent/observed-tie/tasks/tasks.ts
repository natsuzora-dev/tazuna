import { bag, emit, entity, parseInstant, service } from "@natsuzora-dev/tazuna";
import { z } from "zod";

export const Task = entity({ description: "A task", fields: { id: z.string() }, key: "id" });

export const { command, query, machine, event, createEvent, contract, scenario } = service({
  name: "tasks",
  description: "Two clocks each add a task at 10:00",
  entities: { Task },
});

export const armed = event({});
export const taskAdded = createEvent({ entity: Task });

export const arm = command({ emits: [armed] }).decide(() => [emit(armed, {})]);

export const addTask = command({
  input: { taskId: Task.fields.id },
  emits: [taskAdded],
}).decide(({ input }) => [emit(taskAdded, { id: input.taskId })]);

export const taskIds = query({
  output: { taskIds: bag(Task.fields.id) },
}).resolve(({ records }) => ({ taskIds: records.Task.map((t) => t.id) }));

export const first = machine({
  description: `Add task a at 10:00 once armed`,
  receives: { armed },
  commands: { addTask },
  initial: "idle",
  states: { idle: {}, waiting: {}, adding: {}, done: { type: "final" } },
}).chart({
  states: {
    idle: { on: { armed: [{ target: "waiting" }] } },
    waiting: {
      after: { due: { at: () => parseInstant("2026-10-25T01:00:00Z"), onFired: [{ target: "adding" }] } },
    },
    adding: {
      sends: {
        addTask: {
          input: () => ({ taskId: "a" }),
          onAccepted: [{ target: "done" }],
          onRejected: [{ target: "done" }],
        },
      },
    },
  },
});

export const second = machine({
  description: `Add task b at 10:00 once armed`,
  receives: { armed },
  commands: { addTask },
  initial: "idle",
  states: { idle: {}, waiting: {}, adding: {}, done: { type: "final" } },
}).chart({
  states: {
    idle: { on: { armed: [{ target: "waiting" }] } },
    waiting: {
      after: { due: { at: () => parseInstant("2026-10-25T01:00:00Z"), onFired: [{ target: "adding" }] } },
    },
    adding: {
      sends: {
        addTask: {
          input: () => ({ taskId: "b" }),
          onAccepted: [{ target: "done" }],
          onRejected: [{ target: "done" }],
        },
      },
    },
  },
});

export const tasks = contract({ arm, taskIds });
