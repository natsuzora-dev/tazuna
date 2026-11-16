import { emit, entity, ref, service } from "@natsuzora-dev/tazuna";
import { z } from "zod";

export const Task = entity({ description: "A task", fields: { id: z.string() }, key: "id" });
export const Seen = entity({
  description: "A task the service saw",
  fields: { id: z.string(), taskId: z.string() },
  key: "id",
});

export const { automation, command, query, createEvent, deleteEvent, event, contract, scenario } = service({
  description: "Keep the tasks and the tasks seen",
  entities: { Task, Seen },
});

export const taskAdded = createEvent({ entity: Task });
export const seenRecorded = createEvent({ entity: Seen });
export const seen = event({ payload: { id: ref(Seen), taskId: ref(Task) } });
export const forgotten = deleteEvent({ entity: Seen });

export const addTask = command({
  input: { taskId: Task.fields.id },
  emits: [taskAdded],
}).decide(({ input }) => [emit(taskAdded, { id: input.taskId })]);

export const see = command({
  input: { id: Seen.fields.id, taskId: Seen.fields.taskId },
  emits: [seenRecorded, seen],
}).decide(({ input }) => [emit(seenRecorded, input), emit(seen, input)]);

export const seeAdded = automation({
  receives: { taskAdded },
  commands: { see },
}).send({ input: ({ payload, createKey }) => ({ id: createKey(ref(Seen)), taskId: payload.id }) });

export const forget = command({
  input: { id: ref(Seen) },
  emits: [forgotten],
}).decide(({ input }) => [emit(forgotten, { id: input.id })]);

export const seenOf = query({
  input: { taskId: Task.fields.id },
  output: { id: ref(Seen) },
}).resolve(({ input, records }) => {
  const one = records.Seen.filter((s) => s.taskId === input.taskId);
  return { id: one.size === 1 ? (one.only()?.id ?? "") : "" };
});

export const todo = contract({ addTask, seen, forget, seenOf });
