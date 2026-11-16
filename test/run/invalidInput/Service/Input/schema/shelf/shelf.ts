import { any, service, set } from "@natsuzora-dev/tazuna";
import { z } from "zod";
import { catalog } from "../catalog/contract.ts";

export const { machine, screen } = service({ description: "Show numbered items and pick names" });

export const stocker = machine({
  description: "Ask for the numbered items when the service starts",
  queries: { numbers: catalog.numbers },
  initial: "asking",
  states: { asking: {}, known: { type: "final" } },
}).chart({
  states: { asking: { calls: { numbers: { onFulfilled: [{ target: "known" }], onRejected: [{ target: "known" }] } } } },
});

export const shelfScreen = screen({
  description: "Pick a set of names",
  context: { picked: set(z.string()).default([]) },
  controls: { pick: { label: "Pick", payload: { names: set(z.string()) } } },
  initial: "picking",
  states: { picking: {} },
}).chart({
  offers: { pick: any },
  states: { picking: { on: { pick: [{ assign: { picked: ({ payload }) => payload.names } }] } } },
});
