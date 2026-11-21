import { domain, explore } from "@natsuzora-dev/tazuna";
import { markRow, Signal, Task } from "./todo.ts";

export const todoExplore = explore({
  service: "todo",
  depth: 2,
  domains: [
    domain(Task.fields.id, ["task-1"]),
    domain(Signal.fields.id, ["signal-1"]),
    domain(markRow.input.name, ["fulfilled"]),
  ],
});
