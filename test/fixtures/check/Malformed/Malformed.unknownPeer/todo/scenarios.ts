import { external, parseInstant, skip, unchecked } from "@natsuzora-dev/tazuna";
import { calendar } from "../calendar/contract.ts";
import { notifier } from "../notifier/contract.ts";
import { todo } from "./contract.ts";
import { addTask, scenario } from "./todo.ts";

export const listsUnknownPeers = scenario({
  description:
    "List todo itself and an object that is no contract as peers; check reports unknownPeer for each, the latter with a null service",
  given: {
    start: parseInstant("2026-10-25T10:00:00+09:00"),
    records: { Task: [] },
    peers: [
      external(calendar),
      skip(notifier, "notifier's reactions are its own scenarios"),
      unchecked(skip(todo, "todo is the own service")),
      skip(unchecked({}), "no service"),
    ],
  },
  when: (w) => ({ add: w.client.as("client").send(addTask, { taskId: "task-1", title: "Buy milk" }) }),
  then: () => [],
});
