import { emit, entity, service } from "@natsuzora-dev/tazuna";
import { z } from "zod";

export const Task = entity({ description: "A task", fields: { id: z.string(), title: z.string() }, key: "id" });

export const { command, machine, createEvent, contract } = service({
  description: "Keep the tasks while breaking the invariant of counter",
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
}).chart({ states: { counting: { on: { taskAdded: [{ assign: { count: ({ context }) => context.count + 1 } }] } } } });

export const invariantsBreakingCounter = contract({ addTask });
