import { accepted, answered, fulfilled, parseInstant } from "@natsuzora-dev/tazuna";
import { addTask, given, scenario, taskCount } from "./todo.ts";

const arranged = given({ start: parseInstant("2026-10-25T10:00:00+09:00"), records: { Task: [] }, peers: [] });

export const recordsStay = scenario({
  description:
    "Add t1, restart, call taskCount, and send that addTask again with the same id; the record of t1 stays, so taskCount answers 1, and the kept answer of the addTask answers the resent command without a second taskAdded",
  given: arranged,
  when: (w) => {
    const adding = w.client.as("client").send(addTask, { taskId: "t1" });
    w.clock.at(parseInstant("2026-10-25T10:05:00+09:00"));
    w.host.restart();
    const counting = w.client.as("client").call(taskCount, {});
    const resent = w.client.resend(adding);
    return { counting, resent };
  },
  then: ({ counting, resent }) => [answered(counting, fulfilled({ count: 1 })), answered(resent, accepted())],
});

export const subscriptionsEnd = scenario({
  description:
    "Subscribe to taskCount, restart, and add t1; the restart drops the subscription, so adding t1 sends no answer to it",
  given: arranged,
  when: (w) => {
    const counting = w.client.as("client").subscribe(taskCount, {});
    w.host.restart();
    w.client.as("client").send(addTask, { taskId: "t1" });
    return { counting };
  },
  then: ({ counting }) => [answered(counting, [fulfilled({ count: 0 })])],
});
