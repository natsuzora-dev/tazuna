import { any, none } from "@natsuzora-dev/tazuna";
import { z } from "zod";
import { todo } from "../todo/contract.ts";
import { screen } from "./data.ts";

export const listScreen = screen({
  description: "Rows that a user marks; a row that is not marked can be refreshed",
  queries: { tasks: todo.tasks },
  commands: { completeTask: todo.completeTask },
  controls: {
    mark: { label: "Mark", payload: { taskId: z.string() } },
    refresh: { label: "Refresh" },
  },
  initial: "showing",
  states: {
    showing: {
      initial: "rows",
      states: {
        rows: {
          type: "map",
          key: { taskId: z.string() },
          initial: "row",
          states: { row: { initial: "plain", states: { plain: {}, marked: {} } } },
        },
      },
    },
  },
}).chart({
  offers: { mark: any, refresh: none },
  states: {
    showing: { shows: { tasks: {} } },
    rows: { items: ({ shown }) => (shown.tasks?.taskIds ?? []).map((taskId) => ({ taskId })) },
    row: { offers: { refresh: () => [{}] } },
    plain: { on: { mark: [{ target: "marked" }] } },
    marked: { offers: { refresh: none } },
  },
});
