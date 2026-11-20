import { service } from "@natsuzora-dev/tazuna";
import { metronome } from "../metronome/contract.ts";

export const { contract, machine } = service({ name: "listener", description: "Hear the metronome" });

export const hearing = machine({
  description: "Hear ticks, tocks and marks",
  receives: { tick: metronome.tick, tock: metronome.tock, marked: metronome.marked },
  initial: "hearing",
  states: { hearing: {} },
}).chart({
  states: {
    hearing: { on: { tick: [{ target: "hearing" }], tock: [{ target: "hearing" }], marked: [{ target: "hearing" }] } },
  },
});
