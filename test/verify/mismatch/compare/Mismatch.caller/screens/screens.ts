import { any, ref } from "@natsuzora-dev/tazuna";
import { z } from "zod";
import { todo } from "../todo/contract.ts";
import { Draft, screen } from "./data.ts";

export const linkScreen = screen({
  description: "Two new drafts linked both ways, and the first draft pointed at alone",
  context: { first: z.string().default(""), second: z.string().default("") },
  queries: { linked: todo.linked },
  controls: { draft: { label: "Draft" }, point: { label: "Point at the first" } },
  initial: "list",
  states: { list: {} },
}).chart({
  offers: { draft: any, point: any },
  states: {
    list: {
      on: {
        draft: [
          {
            assign: {
              first: ({ createKey }) => createKey(ref(Draft)),
              second: ({ createKey }) => createKey(ref(Draft)),
            },
          },
        ],
        point: [{ assign: { second: () => "" } }],
      },
      shows: {
        linked: {
          input: ({ context }) => ({
            links: [
              { from: context.first, to: context.second },
              { from: context.second, to: context.first },
            ],
          }),
        },
      },
    },
  },
});
