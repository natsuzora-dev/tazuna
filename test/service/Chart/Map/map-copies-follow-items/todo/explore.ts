import { domain, explore, instant, parseInstant } from "@natsuzora-dev/tazuna";
import { note, Task } from "./todo.ts";

export const todoExplore = explore({
  service: "todo",
  depth: 2,
  domains: [
    domain(Task.fields.id, ["task-1"]),
    domain(note.input.text, ["task-1"]),
    domain(instant, [parseInstant("2026-10-26T00:00:00Z")]),
  ],
});
