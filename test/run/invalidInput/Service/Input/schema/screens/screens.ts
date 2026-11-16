import { any, service } from "@natsuzora-dev/tazuna";
import { z } from "zod";

export const { screen } = service({ description: "Show the tasks" });

export const counterScreen = screen({
  description: "A counter the user sets",
  context: { count: z.number().default(0) },
  controls: { countSet: { label: "Count", payload: { count: z.number().int() } } },
  initial: "counting",
  states: { counting: {} },
}).chart({
  offers: { countSet: any },
  states: { counting: { on: { countSet: [{ assign: { count: ({ payload }) => payload.count } }] } } },
});
