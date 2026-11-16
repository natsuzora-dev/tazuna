import { service } from "@natsuzora-dev/tazuna";

export const { machine, scenario } = service({ description: "Keep the tasks" });

export const rounds = machine({
  description: "Start a round again as soon as it is done",
  initial: "round",
  states: { round: { initial: "finished", states: { finished: { type: "final" } } } },
}).chart({
  states: { round: { onDone: [{ target: "round", reenter: true }] } },
});
