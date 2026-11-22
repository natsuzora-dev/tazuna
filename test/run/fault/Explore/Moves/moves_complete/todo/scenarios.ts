import { parseInstant } from "@natsuzora-dev/tazuna";
import { flag, given, scenario } from "./todo.ts";

export const noted = scenario({
  description:
    "Flag a task as not urgent with a note; the explored request with the domain's id, urgent true, and no note fails urgentNoted",
  given: given({ start: parseInstant("2026-10-25T10:00:00+09:00"), records: { Task: [] }, peers: [] }),
  when: (w) => {
    w.client.send(flag, { taskId: "task-1", urgent: false, note: "Call back" });
  },
  then: () => [],
});
