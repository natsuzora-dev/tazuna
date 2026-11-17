import { any, entity, ref, service } from "@natsuzora-dev/tazuna";
import { z } from "zod";
import { todo } from "../todo/contract.ts";

export const Draft = entity({ description: "A draft note", fields: { id: z.string() }, key: "id" });

export const { screen, scenario } = service({
  name: "screens",
  description: "Show the links between notes",
  entities: { Draft },
});

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
