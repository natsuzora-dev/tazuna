import { addComment, addTask, deleteTask, deleteTaskAndComments, pinTask, scenario } from "./todo.ts";

export const deleteCommented = scenario({
  description:
    "Delete a task with two comments by deleteTaskAndComments, which deletes the comments in any order and then the task, leaving no dangling ref; no violation",
  given: { start: "2026-10-25T09:00:00+09:00", records: { Task: [], Comment: [], Pin: { taskId: null } }, peers: [] },
  when: (w) => {
    w.client.send(addTask, { taskId: "task-1", title: "Buy milk" });
    w.client.send(addComment, { commentId: "comment-1", taskId: "task-1" });
    w.client.send(addComment, { commentId: "comment-2", taskId: "task-1" });
    w.client.send(deleteTaskAndComments, { taskId: "task-1" });
  },
  then: () => [],
});

export const deleteCommentedTaskOnly = scenario({
  description:
    "Delete a task with a comment by deleteTask; the comment keeps referring to the deleted task, so test reports danglingRef",
  given: { start: "2026-10-25T09:00:00+09:00", records: { Task: [], Comment: [], Pin: { taskId: null } }, peers: [] },
  when: (w) => {
    w.client.send(addTask, { taskId: "task-1", title: "Buy milk" });
    w.client.send(addComment, { commentId: "comment-1", taskId: "task-1" });
    w.client.send(deleteTask, { taskId: "task-1" });
  },
  then: () => [],
});

export const deletePinned = scenario({
  description:
    "Delete the pinned task by deleteTask; Pin keeps referring to the deleted task, so test reports danglingSingleRef",
  given: { start: "2026-10-25T09:00:00+09:00", records: { Task: [], Comment: [], Pin: { taskId: null } }, peers: [] },
  when: (w) => {
    w.client.send(addTask, { taskId: "task-1", title: "Buy milk" });
    w.client.send(pinTask, { taskId: "task-1" });
    w.client.send(deleteTask, { taskId: "task-1" });
  },
  then: () => [],
});
