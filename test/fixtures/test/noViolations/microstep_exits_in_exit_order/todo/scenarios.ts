import { parseInstant } from "@natsuzora-dev/tazuna";
import { addTask, given, scenario } from "./todo.ts";

const arranged = given({ start: parseInstant("2026-10-25T10:00:00+09:00"), records: {}, peers: [] });

export const fromAToB = scenario({
  description:
    "Add a task; in the transition from a to b, tracer exits descendants first and enters ancestors first, so it writes to steps in this order: the exit of a1, the exit of a, the assign of the transition, the entry of b, and the entry of b1",
  given: arranged,
  when: (w) => {
    w.client.as("client").send(addTask, {});
  },
  then: () => [],
});
