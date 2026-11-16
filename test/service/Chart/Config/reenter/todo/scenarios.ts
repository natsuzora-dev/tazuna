import { deadline } from "@natsuzora-dev/tazuna";
import {
  keepsDeadline,
  keepsDeadlineInParallel,
  keepsDeadlineToChild,
  restartsDeadline,
  restartsDeadlineToChild,
} from "./machines.ts";
import { addTask, scenario } from "./todo.ts";

export const addedThrice = scenario(
  "Add tasks at 10:00, 10:50, and 11:30; keepsDeadline, keepsDeadlineToChild, and keepsDeadlineInParallel do not exit waiting on their reenter: false transitions to waiting, to its child noted, and to the child noted of a region of the parallel state waiting, so they keep the deadline and notify at 11:00. restartsDeadline and restartsDeadlineToChild restart the deadline each time they reenter waiting on a reenter: true transition, and notify at 12:30, an hour after the last addTask. The clock lines order the deadlines due at one time: keepsDeadline, keepsDeadlineToChild, and keepsDeadlineInParallel at 11:00, and restartsDeadline and restartsDeadlineToChild at 12:30",
  {
    given: { start: "2026-10-25T10:00:00+09:00", records: {}, peers: {} },
    when: (w) => {
      w.client.send(addTask, { taskId: "task-1" });
      w.clock.at("2026-10-25T10:50:00+09:00");
      w.client.send(addTask, { taskId: "task-2" });
      w.clock.at("2026-10-25T11:30:00+09:00", {
        order: [
          deadline(keepsDeadline, "waiting", "hour"),
          deadline(keepsDeadlineToChild, "waiting", "hour"),
          deadline(keepsDeadlineInParallel, "waiting", "hour"),
        ],
      });
      w.client.send(addTask, { taskId: "task-3" });
      w.clock.at("2026-10-25T13:00:00+09:00", {
        order: [deadline(restartsDeadline, "waiting", "hour"), deadline(restartsDeadlineToChild, "waiting", "hour")],
      });
    },
    then: () => [],
  },
);
