import { emit, entity, service, singleEntity } from "@natsuzora-dev/tazuna";
import { z } from "zod";

export const Task = entity({ description: "A task", fields: { id: z.string(), title: z.string() }, key: "id" });

export const Stats = singleEntity({ description: "Statistics of tasks", fields: { added: z.number().default(0) } });

export const { automation, command, createEvent, updateEvent } = service({
  description: "Keep the tasks and count the short ones",
  entities: { Task, Stats },
});

export const taskAdded = createEvent({ entity: Task });
export const statsChanged = updateEvent({ entity: Stats, writes: ["added"] });

export const addTask = command({
  input: { taskId: Task.fields.id, title: Task.fields.title },
  emits: [taskAdded],
}).decide(({ input }) => [emit(taskAdded, { id: input.taskId, title: input.title })]);

export const countAdded = command({
  input: { title: Task.fields.title },
  emits: [statsChanged],
  requires: { short: ({ input }) => input.title.length <= 10 },
}).decide(({ records }) => [emit(statsChanged, { added: records.Stats.added + 1 })]);

export const countAddedTask = automation({
  receives: { taskAdded },
  commands: { countAdded },
}).send({
  guard: { short: ({ payload }) => payload.title.length <= 10 },
  input: ({ payload }) => ({ title: payload.title }),
});
