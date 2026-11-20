import { given, listTasks, scenario } from "./todo.ts";

const arranged = given({ start: "2026-10-25T10:00:00+09:00", records: {}, peers: [] });

export const listed = scenario({
  description:
    "List the tasks; decide writes the titles and the entries of tasksListed out of order, and tazuna sorts the titles bag by canonical JSON and the entries by day, the two entries of day 1 by canonical JSON",
  given: arranged,
  when: (w) => {
    w.client.send(listTasks, {});
  },
  then: () => [],
});
