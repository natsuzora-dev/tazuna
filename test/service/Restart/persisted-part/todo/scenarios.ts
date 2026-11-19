import { accepted, answered, emitted, fulfilled } from "@natsuzora-dev/tazuna";
import { addTask, scenario, taskCount } from "./todo.ts";

const given = { start: "2026-10-25T10:00:00+09:00", records: { Task: [] }, peers: {} } as const;

export const recordsStay = scenario(
  "Add t1, restart, call taskCount, and send that addTask again with the same id; the record of t1 stays, so taskCount answers 1, and the kept answer of the addTask answers the resent command without a second taskAdded",
  {
    given,
    when: (w) => {
      const adding = w.client.send(addTask, { taskId: "t1" });
      w.clock.at("2026-10-25T10:05:00+09:00");
      w.host.restart();
      const counting = w.client.call(taskCount, {});
      const resent = w.client.resend(adding);
      return { counting, resent };
    },
    then: ({ counting, resent }) => [
      answered(counting, fulfilled({ count: 1 })),
      answered(resent, accepted),
      emitted(resent, []),
    ],
  },
);

export const subscriptionsEnd = scenario(
  "Subscribe to taskCount, restart, and add t1; the restart drops the subscription, so adding t1 sends no answer to it",
  {
    given,
    when: (w) => {
      const counting = w.client.subscribe(taskCount, {});
      w.host.restart();
      w.client.send(addTask, { taskId: "t1" });
      return { counting };
    },
    then: ({ counting }) => [answered(counting, [fulfilled({ count: 0 })])],
  },
);
