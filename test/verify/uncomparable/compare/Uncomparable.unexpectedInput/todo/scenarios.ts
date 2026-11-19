import { external } from "@natsuzora-dev/tazuna";
import { calendar } from "../calendar/contract.ts";
import { addTask, given, scenario } from "./todo.ts";

const arranged = given({
  start: "2026-10-25T00:00:00Z",
  records: { Task: [] },
  peers: [external(calendar)],
});

export const addOne = scenario({
  description: "Add a task; the implementation trace adds a second task that the snapshot does not",
  given: arranged,
  when: (w) => {
    w.net.leaveInFlight(w.client.send(addTask, { taskId: "task-1", title: "Buy milk" }).request(calendar.nextDay));
  },
  then: () => [],
});
