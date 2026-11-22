import { parseInstant } from "@natsuzora-dev/tazuna";
import { given, mark, scenario } from "./todo.ts";

export const marked = scenario({
  description:
    "Mark a task open; Zod writes Status, registered with an id, as a $ref, and the explored request takes each of its values, so done fails stillOpen",
  given: given({ start: parseInstant("2026-10-25T10:00:00+09:00"), records: { Task: [] }, peers: [] }),
  when: (w) => {
    w.client.send(mark, { taskId: "task-1", status: "open" });
  },
  then: () => [],
});
