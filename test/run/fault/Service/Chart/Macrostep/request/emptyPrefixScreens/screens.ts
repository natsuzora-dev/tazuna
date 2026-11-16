import { service } from "@natsuzora-dev/tazuna";
import { todo } from "../todo/contract.ts";

export const { screen } = service({ description: "Show the tasks whose title starts with an empty prefix" });

export const titledScreen = screen({
  description: "The tasks whose title starts with a prefix",
  queries: { titled: todo.titled },
  initial: "showing",
  states: { showing: {} },
}).chart({
  states: { showing: { shows: { titled: { input: () => ({ prefix: "" }) } } } },
});
