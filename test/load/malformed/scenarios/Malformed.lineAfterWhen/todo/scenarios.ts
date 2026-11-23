import { parseInstant } from "@natsuzora-dev/tazuna";
import { addTask, scenario } from "./todo.ts";

export const placesLineInThen = scenario({
  description: "Keep the actors of When and place a line from Then; check reports lineAfterWhen",
  given: { start: parseInstant("2026-10-25T10:00:00+09:00"), records: { Task: [] }, peers: [] },
  when: (w) => ({ w }),
  then: ({ w }) => {
    w.client.as("client").send(addTask, { taskId: "task-1", title: "Buy milk" });
    return [];
  },
});
