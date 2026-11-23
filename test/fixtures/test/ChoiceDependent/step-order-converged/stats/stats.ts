import { emit, entity, service, singleEntity } from "@natsuzora-dev/tazuna";
import { z } from "zod";

export const Task = entity({ description: "A task", fields: { id: z.string(), title: z.string() }, key: "id" });

export const Stats = singleEntity({
  description: "Statistics of tasks",
  fields: { added: z.int().default(0), lastTitle: z.string().default("") },
});

export const { automation, command, createEvent, updateEvent, contract, scenario } = service({
  name: "stats",
  description: "Keep the tasks and their statistics",
  entities: { Task, Stats },
});

export const taskAdded = createEvent({ entity: Task });

export const addTask = command({
  callers: ["client"],
  input: { taskId: Task.fields.id, title: Task.fields.title },
  emits: [taskAdded],
}).decide(({ input }) => [emit(taskAdded, { id: input.taskId, title: input.title })]);

export const statsChanged = updateEvent({
  entity: Stats,
  writes: ["added", "lastTitle"],
});

export const countAdded = command({ callers: ["client", "stats"], emits: [statsChanged] }).decide(({ records }) => [
  emit(statsChanged, { added: records.Stats.added + 1, lastTitle: records.Stats.lastTitle }),
]);

export const rememberTitle = command({
  callers: ["client", "stats"],
  input: { title: Task.fields.title },
  emits: [statsChanged],
}).decide(({ input, records }) => [emit(statsChanged, { added: records.Stats.added, lastTitle: input.title })]);

export const countAddedTask = automation({
  receives: { taskAdded },
  commands: { countAdded },
}).send({});

export const rememberAddedTitle = automation({
  receives: { taskAdded },
  commands: { rememberTitle },
}).send({ input: ({ payload }) => ({ title: payload.title }) });

export const stats = contract({ addTask });
