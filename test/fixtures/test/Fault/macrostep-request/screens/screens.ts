import { service } from "@natsuzora-dev/tazuna";
import { todo } from "../todo/contract.ts";

export const { screen, scenario } = service({ name: "screens", description: "Show the tasks" });

export const titledScreen = screen({
  description: "The tasks whose title starts with a prefix",
  queries: { titled: todo.titled },
  initial: "showing",
  states: { showing: {} },
}).chart({
  states: { showing: { shows: { titled: { input: () => ({ prefix: "B" }) } } } },
});
