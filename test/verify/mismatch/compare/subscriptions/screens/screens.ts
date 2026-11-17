import { any, service } from "@natsuzora-dev/tazuna";
import { z } from "zod";
import { todo } from "../todo/contract.ts";

export const { screen, scenario } = service({ name: "screens", description: "Show the tasks" });

export const taskListScreen = screen({
  description: "The titles of the tasks that start with a prefix",
  context: { prefix: z.string().default("") },
  queries: { tasksNamed: todo.tasksNamed },
  controls: { filter: { label: "Filter", payload: { prefix: z.string() } }, close: { label: "Close" } },
  initial: "list",
  states: { list: {}, closed: { type: "final" } },
}).chart({
  offers: { filter: any, close: any },
  states: {
    list: {
      on: { filter: [{ assign: { prefix: ({ payload }) => payload.prefix } }], close: [{ target: "closed" }] },
      shows: { tasksNamed: { input: ({ context }) => ({ prefix: context.prefix }) } },
    },
  },
});
