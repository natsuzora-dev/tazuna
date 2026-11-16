import { constants, emit, entity, ref, service, set } from "@natsuzora-dev/tazuna";
import { z } from "zod";

const Task = entity({ description: "A task", fields: { id: z.string() }, key: "id" });

export const Mark = entity({
  description: "A mark on a task",
  fields: { id: z.string(), taskId: ref(Task) },
  key: "id",
});

export const { automation, command, createEvent, event, machine, query, contract } = service({
  description: "Keep the tasks, whose entity and two definitions are not exported",
  entities: { Task, Mark },
});

export const taskAdded = createEvent({ entity: Task });
const taskSeen = event({});

export const addTask = command({
  input: { taskId: z.string() },
  emits: [taskAdded, taskSeen],
}).decide(({ input }) => [emit(taskAdded, { id: input.taskId }), emit(taskSeen, {})]);

const markSeen = command({ emits: [] }).decide(() => []);

export const seenMarked = automation({ receives: { taskSeen }, commands: { markSeen } }).send({});

const { event: noteEvent } = service({ description: "Keep the notes" });

export const noted = noteEvent({});

export const watcher = machine({
  description: "Watch the seen tasks and the notes, of which the notes event has no exported definer",
  receives: { taskSeen, noted },
  commands: { markSeen },
  initial: "watching",
  states: { watching: {}, seen: {} },
}).chart({ states: { watching: { on: { taskSeen: [{ target: "seen" }], noted: [{ target: "seen" }] } } } });

export const taskNoted = event({ payload: { taskId: ref(Task) } });

export const taskDetail = query({ input: { taskId: ref(Task) }, output: { related: set(ref(Task)) } }).resolve(() => ({
  related: [],
}));

export const todo = contract({ TaskId: ref(Task) });

export const todoConstants = constants(z.object({ defaultTaskId: ref(Task) }), { defaultTaskId: "task-1" });
