import { celebrate, machine, milkBought, roomDusted } from "./todo.ts";

export const chores = machine({
  description: "Celebrate once when both the shopping and the cleaning are done",
  receives: { milkBought, roomDusted },
  commands: { celebrate },
  initial: "working",
  states: {
    working: {
      type: "parallel",
      states: {
        shopping: { initial: "buying", states: { buying: {}, bought: { type: "final" } } },
        cleaning: { initial: "dusting", states: { dusting: {}, dusted: { type: "final" } } },
      },
    },
    celebrating: {},
    stopped: { type: "final" },
  },
}).chart({
  states: {
    working: { onDone: [{ target: "celebrating" }] },
    buying: { on: { milkBought: [{ target: "bought" }] } },
    dusting: { on: { roomDusted: [{ target: "dusted" }] } },
    celebrating: { sends: { celebrate: { onAccepted: [{ target: "stopped" }] } } },
  },
});
