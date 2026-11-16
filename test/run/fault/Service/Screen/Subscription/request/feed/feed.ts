import { service } from "@natsuzora-dev/tazuna";
import { todo } from "../todo/contract.ts";

export const { screen, scenario } = service({ description: "Show the recent tasks" });

export const recentScreen = screen({
  description: "The recent tasks",
  queries: { recent: todo.recent },
  initial: "showing",
  states: { showing: {} },
}).chart({
  states: { showing: { shows: { recent: { input: () => ({ limit: 0 }) } } } },
});
