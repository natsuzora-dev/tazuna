import { emit, entity, ref, service, singleEntity } from "@natsuzora-dev/tazuna";
import { z } from "zod";

export const Task = entity({ description: "A task", fields: { id: z.string(), title: z.string() }, key: "id" });

export const Comment = entity({
  description: "A comment on a task",
  fields: { id: z.string(), taskId: ref(Task) },
  key: "id",
});

export const Pin = singleEntity({
  description: "The pinned task",
  fields: { taskId: ref(Task).nullable().default(null) },
});

export const { command, createEvent, deleteEvent, updateEvent, contract } = service({
  description: "Keep the tasks",
  entities: { Task, Comment, Pin },
});

export const taskAdded = createEvent({ entity: Task });

export const addTask = command({
  input: { taskId: Task.fields.id, title: Task.fields.title },
  emits: [taskAdded],
}).decide(({ input }) => [emit(taskAdded, { id: input.taskId, title: input.title })]);

export const commentAdded = createEvent({ entity: Comment });

export const taskDeleted = deleteEvent({ entity: Task });

export const commentDeleted = deleteEvent({ entity: Comment });

export const addComment = command({
  input: { commentId: Comment.fields.id, taskId: ref(Task) },
  emits: [commentAdded],
}).decide(({ input }) => [emit(commentAdded, { id: input.commentId, taskId: input.taskId })]);

export const deleteTaskAndComments = command({
  input: { taskId: ref(Task) },
  emits: [taskDeleted, commentDeleted],
}).decide(({ input, records }) => [
  records.Comment.filter((c) => c.taskId === input.taskId).map((c) => emit(commentDeleted, { id: c.id })),
  emit(taskDeleted, { id: input.taskId }),
]);

export const deleteTask = command({
  input: { taskId: ref(Task) },
  emits: [taskDeleted, commentDeleted],
}).decide(({ input }) => [emit(taskDeleted, { id: input.taskId })]);

export const taskPinned = updateEvent({ entity: Pin, writes: ["taskId"] });

export const pinTask = command({
  input: { taskId: ref(Task) },
  emits: [taskPinned],
}).decide(({ input }) => [emit(taskPinned, { taskId: input.taskId })]);

export const todo = contract({ addTask, addComment, deleteTaskAndComments, deleteTask, pinTask });
