import { external, parseInstant } from "@natsuzora-dev/tazuna";
import { calendar } from "../calendar/contract.ts";
import { addDoneTask, given, scenario } from "./todo.ts";

const arranged = given({ start: parseInstant("2026-10-25T10:00:00+09:00"), records: {}, peers: [external(calendar)] });

export const passThrough = scenario({
  description:
    "Add a done task; in the one message of addDoneTask, dayNoter enters asking on taskAdded and exits it on taskCompleted. It is not in asking at the end of the macrostep, so it sends no calendar.nextDay",
  given: arranged,
  when: (w) => {
    w.client.as("client").send(addDoneTask, { taskId: "task-1" });
  },
  then: () => [],
});
