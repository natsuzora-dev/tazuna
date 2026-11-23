import { emit, entity, service, singleEntity } from "@natsuzora-dev/tazuna";
import { z } from "zod";

export const Task = entity({
  description: "A task",
  fields: { id: z.string(), title: z.string() },
  key: "id",
  invariants: { titleNotBlank: ({ record }) => record.title !== "" },
});

export const Tally = singleEntity({
  description: "The number of added tasks",
  fields: { added: z.int().default(0) },
  invariants: { belowTwo: ({ record }) => record.added < 2 },
});

export const { command, createEvent, updateEvent, contract, scenario } = service({
  name: "invariantsBreakingTodo",
  description: "Keep the tasks while breaking the invariants of Task, Tally, and the service",
  entities: { Task, Tally },
});

export const taskAdded = createEvent({ entity: Task });

export const tallyCounted = updateEvent({ entity: Tally, writes: ["added"] });

export const addTask = command({
  callers: ["client"],
  input: { taskId: Task.fields.id, title: Task.fields.title },
  emits: [taskAdded, tallyCounted],
}).decide(({ input, records }) => [
  emit(taskAdded, { id: input.taskId, title: input.title }),
  emit(tallyCounted, { added: records.Tally.added + 1 }),
]);

export const invariantsBreakingTodo = contract({ addTask });
