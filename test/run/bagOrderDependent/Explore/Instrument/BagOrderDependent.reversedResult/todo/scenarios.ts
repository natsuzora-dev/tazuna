import { parseInstant } from "@natsuzora-dev/tazuna";
import { addTask, scenario, titles, titlesInArray } from "./todo.ts";

export const addTwo = scenario({
  description: "Add two tasks and read their titles; no violation",
  given: { start: parseInstant("2026-10-25T09:00:00+09:00"), records: { Task: [] }, peers: [] },
  when: (w) => {
    w.client.send(addTask, { taskId: "task-1", title: "Buy milk" });
    w.client.send(addTask, { taskId: "task-2", title: "Buy eggs" });
    w.client.call(titles, {});
  },
  then: () => [],
});

export const addTwoAndReadArray = scenario({
  description:
    "Add two tasks and push their titles to an array from a Bag callback; the output changes when the Bag visits the records in reverse order, so test reports reversedResult",
  given: { start: parseInstant("2026-10-25T09:00:00+09:00"), records: { Task: [] }, peers: [] },
  when: (w) => {
    w.client.send(addTask, { taskId: "task-1", title: "Buy milk" });
    w.client.send(addTask, { taskId: "task-2", title: "Buy eggs" });
    w.client.call(titlesInArray, {});
  },
  then: () => [],
});
