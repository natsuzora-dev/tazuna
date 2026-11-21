import { domain, explore } from "@natsuzora-dev/tazuna";
import { Task } from "./todo.ts";

export const emptyTitleTodoExplore = explore({
  service: "emptyTitleTodo",
  depth: 2,
  domains: [domain(Task.fields.id, ["task-1"])],
});
