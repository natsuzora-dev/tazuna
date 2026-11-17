import { emit, entity, service } from "@natsuzora-dev/tazuna";
import { z } from "zod";

export const Task = entity({ description: "A task", fields: { id: z.string(), title: z.string() }, key: "id" });

export const { command, machine, createEvent, contract, scenario } = service({
  name: "todo",
  description: "Keep the tasks",
  entities: { Task },
});

export const taskAdded = createEvent({ entity: Task });

export const addTask = command({
  input: { taskId: Task.fields.id, title: Task.fields.title },
  emits: [taskAdded],
}).decide(({ input }) => [emit(taskAdded, { id: input.taskId, title: input.title })]);

export const counter = machine({
  description: "Count added tasks up to one",
  context: { count: z.number().default(0) },
  receives: { taskAdded },
  initial: "counting",
  states: { counting: {} },
  invariants: { atMostOne: ({ context }) => context.count <= 1 },
}).chart({
  states: {
    counting: {
      on: {
        taskAdded: [
          {
            guard: { first: ({ context }) => context.count === 0 },
            assign: { count: ({ context }) => context.count + 1 },
          },
        ],
      },
    },
  },
});

export const todo = contract({ addTask });
