import { emit, entity, ref, service } from "@natsuzora-dev/tazuna";
import { z } from "zod";

export const User = entity({ description: "A user who signs in", fields: { id: z.string() }, key: "id" });

export const Task = entity({
  description: "A task of the user who added it",
  fields: { id: z.string(), ownerId: ref(User) },
  key: "id",
});

export const { command, createEvent, bounds } = service({
  name: "todo",
  description: "Keep each user's tasks",
  entities: { User, Task },
});

export const taskAdded = createEvent({ entity: Task });

// The importer is a service, whose caller has no key, so its task's owner names no user.
export const addTask = command({
  callers: [User, "importer"],
  input: { taskId: Task.fields.id },
  emits: [taskAdded],
}).decide(({ input, caller }) => [emit(taskAdded, { id: input.taskId, ownerId: caller.key ?? "" })]);

export const todoBounds = bounds({ creates: { User: 1, Task: 2 } });
