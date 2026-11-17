import { bag, emit, entity, ref, service } from "@natsuzora-dev/tazuna";
import { z } from "zod";

export const Task = entity({ description: "A task", fields: { id: z.string() }, key: "id" });
export const Seen = entity({
  description: "A task the service saw",
  fields: { id: z.string(), taskId: z.string() },
  key: "id",
});

export const { automation, command, query, createEvent, contract, scenario } = service({
  name: "todo",
  description: "Keep the tasks and the tasks seen",
  entities: { Task, Seen },
});

export const taskAdded = createEvent({ entity: Task });
export const seen = createEvent({ entity: Seen });

export const addTask = command({
  input: { taskId: Task.fields.id },
  emits: [taskAdded],
}).decide(({ input }) => [emit(taskAdded, { id: input.taskId })]);

export const see = command({
  input: { id: Seen.fields.id, taskId: Seen.fields.taskId },
  emits: [seen],
}).decide(({ input }) => [emit(seen, input)]);

export const seeAdded = automation({
  receives: { taskAdded },
  commands: { see },
}).send({ input: ({ payload, createKey }) => ({ id: createKey(ref(Seen)), taskId: payload.id }) });

export const seenIds = query({
  output: {
    repeated: bag(ref(Seen)),
    none: bag(z.string()),
    ids: bag(ref(Seen)),
    listed: z.array(ref(Seen)),
  },
}).resolve(({ records }) => {
  const ids = records.Seen.map((s) => s.id);
  const seenOf = (taskId: string) => records.Seen.filter((s) => s.taskId === taskId).map((s) => s.id);
  const listed = ["task-1", "task-2"].flatMap((taskId) => {
    const one = seenOf(taskId);
    return one.size === 1 ? (one.only() ?? []) : [];
  });
  return { repeated: ids.concat(seenOf("task-1")), none: [], ids, listed };
});

export const todo = contract({ addTask, seenIds });
