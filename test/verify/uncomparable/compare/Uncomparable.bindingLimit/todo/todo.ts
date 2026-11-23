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

export const addTask = command({ callers: ["client"], input: { taskId: Task.fields.id }, emits: [taskAdded] }).decide(
  ({ input }) => [emit(taskAdded, { id: input.taskId })],
);

export const see = command({
  callers: ["client", "todo"],
  input: { id: Seen.fields.id, taskId: Seen.fields.taskId },
  emits: [seen],
}).decide(({ input }) => [emit(seen, input)]);

export const seeAdded = automation({
  receives: { taskAdded },
  commands: { see },
}).send({ input: ({ payload, createKey }) => ({ id: createKey(ref(Seen)), taskId: payload.id }) });

export const seenIds = query({
  callers: ["client"],
  output: {
    repeated: bag(ref(Seen)),
    none: bag(z.string()),
    ids: bag(ref(Seen)),
    listed: z.array(ref(Seen)),
  },
}).resolve(({ records }) => {
  const ids = records.Seen.map((s) => s.id);
  const firstSeen = records.Seen.filter((s) => s.taskId === "task-1").map((s) => s.id);
  const secondSeen = records.Seen.filter((s) => s.taskId === "task-2").map((s) => s.id);
  const firstOnly = firstSeen.size === 1 ? firstSeen.only() : undefined;
  const secondOnly = secondSeen.size === 1 ? secondSeen.only() : undefined;
  const listed = [...(firstOnly === undefined ? [] : [firstOnly]), ...(secondOnly === undefined ? [] : [secondOnly])];
  return { repeated: ids.concat(firstSeen), none: [], ids, listed };
});

export const seenTwice = query({ callers: ["client"], output: { repeated: bag(ref(Seen)) } }).resolve(
  ({ records }) => ({
    repeated: records.Seen.map((s) => s.id).concat(records.Seen.filter((s) => s.taskId === "task-1").map((s) => s.id)),
  }),
);

export const todo = contract({ addTask, seenIds, seenTwice });
