import { domain, explore } from "@natsuzora-dev/tazuna";
import { addTasks, Task } from "./todo.ts";

export const todoExplore = explore({
  service: "todo",
  depth: 2,
  domains: [
    domain(addTasks.input.tasks, [
      [
        { id: "task-1", day: "Mon" },
        { id: "task-2", day: "Mon" },
        { id: "task-3", day: "Mon" },
      ],
    ]),
    domain(Task.fields.id, ["task-1"]),
  ],
});
