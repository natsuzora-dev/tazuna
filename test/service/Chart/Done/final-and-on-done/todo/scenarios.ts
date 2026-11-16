import { buyMilk, dustRoom, scenario } from "./todo.ts";

export const bothDone = scenario(
  "Buy milk, dust the room, and buy milk again; chores enters both shopping and cleaning when it enters working. When buyMilk finishes shopping, chores does not select the onDone of working until cleaning finishes. When dustRoom finishes both, chores goes to celebrating through onDone, celebrates, enters stopped, the final state of root, and stops, so it does not react to the later buyMilk",
  {
    given: { start: "2026-10-25T10:00:00+09:00", records: {}, peers: {} },
    when: (w) => {
      w.client.send(buyMilk, {});
      w.client.send(dustRoom, {});
      w.client.send(buyMilk, {});
    },
    then: () => [],
  },
);
