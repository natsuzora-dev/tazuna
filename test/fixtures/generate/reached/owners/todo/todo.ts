import { emit, entity, ref, service } from "@natsuzora-dev/tazuna";
import { z } from "zod";

export const User = entity({ description: "A user who signs in", fields: { id: z.string() }, key: "id" });

export const Task = entity({
  description: "A task of the user who added it",
  fields: { id: z.string(), ownerId: ref(User) },
  key: "id",
});

export const { command, createEvent, deleteEvent, bounds } = service({
  name: "todo",
  description: "Keep each user's tasks",
  entities: { User, Task },
});

export const userJoined = createEvent({ entity: User });
export const taskAdded = createEvent({ entity: Task });
export const taskDeleted = deleteEvent({ entity: Task });

// Sign-up runs outside the users, so a service sends join; generate sends as it to make a user to call as.
export const join = command({ callers: ["accounts"], input: { userId: User.fields.id }, emits: [userJoined] }).decide(
  ({ input }) => [emit(userJoined, { id: input.userId })],
);

export const addTask = command({
  callers: [User],
  input: { taskId: Task.fields.id },
  emits: [taskAdded],
}).decide(({ input, caller }) => [emit(taskAdded, { id: input.taskId, ownerId: caller.key })]);

export const deleteTask = command({
  callers: [User],
  input: { taskId: ref(Task) },
  emits: [taskDeleted],
  requires: { ownTask: ({ caller, refs }) => refs.taskId.ownerId === caller.key },
}).decide(({ input }) => [emit(taskDeleted, { id: input.taskId })]);

export const todoBounds = bounds({ creates: { User: 2, Task: 1 } });
