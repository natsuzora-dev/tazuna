import { domain, explore } from "@natsuzora-dev/tazuna";
import { Note, Tag, Task } from "./todo.ts";

export const todoExplore = explore({
  service: "todo",
  depth: 2,
  domains: [domain(Task.fields.id, ["task-1"]), domain(Note.fields.id, ["task-1"]), domain(Tag.fields.id, ["task-1"])],
});
