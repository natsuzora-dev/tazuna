import { domain, explore } from "@natsuzora-dev/tazuna";
import { flag, Task } from "./todo.ts";

export const todoExplore = explore({
  service: "todo",
  depth: 1,
  domains: [domain(Task.fields.id, ["task-9"]), domain(flag.input.note, ["Call back"])],
});
