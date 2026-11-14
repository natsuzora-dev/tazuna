import { at, scenario, send } from "@natsuzora-dev/tazuna";
import { addComment, addTask, deleteTask, deleteTaskAndComments, pinTask } from "./todo.ts";

export const deleteCommented = scenario(
  "Delete a task with two comments by deleteTaskAndComments, which deletes the comments in any order and then the task, leaving no dangling ref; no violation",
  [
    at("2026-10-25T09:00:00+09:00"),
    send(addTask, { taskId: "task-1", title: "Buy milk" }),
    send(addComment, { commentId: "comment-1", taskId: "task-1" }),
    send(addComment, { commentId: "comment-2", taskId: "task-1" }),
    send(deleteTaskAndComments, { taskId: "task-1" }),
  ],
);

export const deleteCommentedTaskOnly = scenario(
  "Delete a task with a comment by deleteTask; the comment keeps referring to the deleted task, so test reports danglingRef",
  [
    at("2026-10-25T09:00:00+09:00"),
    send(addTask, { taskId: "task-1", title: "Buy milk" }),
    send(addComment, { commentId: "comment-1", taskId: "task-1" }),
    send(deleteTask, { taskId: "task-1" }),
  ],
);

export const deletePinned = scenario(
  "Delete the pinned task by deleteTask; Pin keeps referring to the deleted task, so test reports danglingSingleRef",
  [
    at("2026-10-25T09:00:00+09:00"),
    send(addTask, { taskId: "task-1", title: "Buy milk" }),
    send(pinTask, { taskId: "task-1" }),
    send(deleteTask, { taskId: "task-1" }),
  ],
);
