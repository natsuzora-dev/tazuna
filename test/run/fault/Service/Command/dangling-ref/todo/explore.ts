import { domain, explore } from "@natsuzora-dev/tazuna";
import { Comment, Task } from "./todo.ts";

export const todoExplore = explore({
  service: "todo",
  depth: 2,
  domains: [
    domain(Task.fields.id, ["task-1"]),
    domain(Task.fields.title, ["Buy milk"]),
    domain(Comment.fields.id, ["comment-1"]),
  ],
});
