import { bag, emit, entity, ref, service } from "@natsuzora-dev/tazuna";
import { z } from "zod";

export const User = entity({ description: "A user who signs in", fields: { id: z.string() }, key: "id" });

export const Task = entity({
  description: "A task of its owner",
  fields: { id: z.string(), ownerId: ref(User), title: z.string() },
  key: "id",
});

export const { command, query, createEvent, deleteEvent, contract, given, scenario } = service({
  name: "todo",
  description: "Keep each user's tasks",
  entities: { User, Task },
});

export const taskAdded = createEvent({ entity: Task });
export const taskDeleted = deleteEvent({ entity: Task });

export const addTask = command({
  callers: [User],
  input: { taskId: Task.fields.id, title: Task.fields.title },
  emits: [taskAdded],
}).decide(({ input, caller }) => [emit(taskAdded, { id: input.taskId, ownerId: caller.key, title: input.title })]);

export const deleteTask = command({
  callers: [User, "janitor"],
  input: { taskId: ref(Task) },
  emits: [taskDeleted],
  requires: { ownTask: ({ caller, refs }) => caller.entity !== "User" || refs.taskId.ownerId === caller.key },
}).decide(({ input }) => [emit(taskDeleted, { id: input.taskId })]);

export const myTasks = query({
  callers: [User],
  output: { titles: bag(Task.fields.title) },
}).resolve(({ caller, records }) => ({
  titles: records.Task.filter((t) => t.ownerId === caller.key).map((t) => t.title),
}));

export const todo = contract({ addTask, deleteTask, myTasks });
