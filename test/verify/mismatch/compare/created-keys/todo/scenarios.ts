import { parseInstant } from "@natsuzora-dev/tazuna";
import { addTask, scenario, seenIds, seenTwice } from "./todo.ts";

export const seenOnce = scenario({
  description:
    "Add a task and ask twice for the seen ids; the key that taskAdded's internal seen event creates binds where the first seenIds answer holds it; no violation",
  given: { start: parseInstant("2026-10-25T00:00:00Z"), records: { Task: [], Seen: [] }, peers: [] },
  when: (w) => {
    w.client.send(addTask, { taskId: "task-1" });
    w.client.call(seenIds, {});
    w.client.call(seenIds, {});
  },
  then: () => [],
});

export const seenOnceWrongListed = scenario({
  description:
    "Same inputs as seenOnce; the implementation trace of this scenario answers the second seenIds with another key in listed, which does not stand for the bound key, so verify reports Mismatch.output",
  given: { start: parseInstant("2026-10-25T00:00:00Z"), records: { Task: [], Seen: [] }, peers: [] },
  when: (w) => {
    w.client.send(addTask, { taskId: "task-1" });
    w.client.call(seenIds, {});
    w.client.call(seenIds, {});
  },
  then: () => [],
});

export const seenMultiplicity = scenario({
  description:
    "Add two tasks and ask for the seen ids with task-1's repeated; the bag [Seen-1, Seen-2, Seen-1] meets the implementation's [x, y, y], and only Seen-1 = y, Seen-2 = x keeps the counts, which the later seenIds answer's listed confirms; no violation",
  given: { start: parseInstant("2026-10-25T00:00:00Z"), records: { Task: [], Seen: [] }, peers: [] },
  when: (w) => {
    w.client.send(addTask, { taskId: "task-1" });
    w.client.send(addTask, { taskId: "task-2" });
    w.client.call(seenTwice, {});
    w.client.call(seenIds, {});
  },
  then: () => [],
});
