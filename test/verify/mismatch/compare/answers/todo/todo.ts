import { bag, contract, datetime, emit, entity, ref, service } from "@natsuzora-dev/tazuna";
import { z } from "zod";

export const Task = entity({
  description: "A task",
  fields: { id: z.string(), title: z.string(), isDone: z.boolean() },
  key: "id",
});

export const { command, query, createEvent, updateEvent } = service({
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
  input: { taskId: ref(Task) },
  emits: [taskCompleted],
  requires: { notDone: ({ input, records }) => records.Task.get(input.taskId)?.isDone === false },
}).decide(({ input }) => [emit(taskCompleted, { id: input.taskId, isDone: true })]);

export const taskTitles = query({
  output: { titles: bag(Task.fields.title) },
}).resolve(({ records }) => ({ titles: records.Task.map((t) => t.title) }));

const part = z.union([z.strictObject({ name: z.string() }), z.strictObject({ size: z.number() })]);

export const taskCard = query({
  output: {
    due: z.strictObject({ at: datetime, parts: z.array(z.strictObject({ name: z.string() })) }),
    mark: z.discriminatedUnion("kind", [
      z.strictObject({ kind: z.literal("one"), part }),
      z.strictObject({ kind: z.literal("many"), parts: z.array(part).optional() }),
    ]),
  },
}).resolve(() => ({
  due: { at: Temporal.Instant.from("2026-10-25T01:00:00Z"), parts: [{ name: "Morning" }] },
  mark: { kind: "one" as const, part: { name: "Shop" } },
}));

export const todo = contract({ addTask, completeTask, taskTitles, taskCard });
