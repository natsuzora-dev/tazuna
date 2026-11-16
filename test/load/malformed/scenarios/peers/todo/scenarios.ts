import { external } from "@natsuzora-dev/tazuna";
import { calendar } from "../calendar/contract.ts";
import { addTask, scenario } from "./todo.ts";

export const listsPeerUnderOtherName = scenario(
  "List calendar under the key cal, and leave out notifier, which receives todo's events; check reports misnamedPeer for cal and unlistedPeer for notifier",
  {
    given: { start: "2026-10-25T10:00:00+09:00", records: { Task: [] }, peers: { cal: external(calendar) } },
    when: (w) => ({ add: w.client.send(addTask, { taskId: "task-1", title: "Buy milk" }) }),
    then: () => [],
  },
);
