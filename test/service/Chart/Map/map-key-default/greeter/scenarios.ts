import { addTasks, given, scenario } from "./greeter.ts";

export const copiesByParsedKey = scenario({
  description:
    "Add task-1 and task-2; the copy key of task-2 gets rank 0 from its default, so the copies run in the order of the parsed keys and greet task-2 first",
  given: given({ start: "2026-10-25T10:00:00+09:00", records: { Task: [] }, peers: [] }),
  when: (w) => {
    w.client.send(addTasks, { taskIds: ["task-1", "task-2"] });
  },
  then: () => [],
});
