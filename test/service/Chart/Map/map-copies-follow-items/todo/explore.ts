import { datetime, domain, explore } from "@natsuzora-dev/tazuna";
import { note, Task } from "./todo.ts";

export const todoExplore = explore({
  service: "todo",
  depth: 2,
  domains: [
    domain(Task.fields.id, ["task-1"]),
    domain(note.input.text, ["task-1"]),
    domain(datetime, ["2026-10-26T00:00:00Z"]),
  ],
});
