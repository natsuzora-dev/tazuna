import { unchecked } from "@natsuzora-dev/tazuna";
import { addTask, scenario } from "./todo.ts";

export const writesInvalidRecords = scenario(
  "Write a task whose title breaks its schema and a record of an entity that todo does not have; check reports invalidRecord for each",
  {
    given: {
      start: "2026-10-25T10:00:00+09:00",
      records: unchecked({ Task: [{ id: "task-1", title: "" }], Note: {} }),
      peers: {},
    },
    when: (w) => ({ add: w.client.send(addTask, { taskId: "task-2", title: "Buy milk" }) }),
    then: () => [],
  },
);
