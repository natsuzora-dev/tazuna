import { domain, explore } from "@natsuzora-dev/tazuna";
import { addNotes, Task } from "./tasks.ts";

export const tasksExplore = explore({
  service: "tasks",
  depth: 2,
  domains: [
    domain(Task.fields.id, ["task-1"]),
    domain(Task.fields.title, ["Buy milk"]),
    domain(addNotes.input.notes, [[]]),
  ],
});
