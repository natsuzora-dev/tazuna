import { any, entity, ref, service } from "@natsuzora-dev/tazuna";
import { z } from "zod";
import { todo } from "../todo/contract.ts";

export const Draft = entity({ description: "A draft note", fields: { id: z.string() }, key: "id" });

export const { screen, scenario } = service({ description: "Show the notes", entities: { Draft } });

export const noteScreen = screen({
  description: "Two new drafts, all of them, and then the first one",
  context: { first: z.string().default(""), second: z.string().default("") },
  queries: { notesIn: todo.notesIn, note: todo.note, notesNamed: todo.notesNamed },
  controls: { draft: { label: "Draft" }, open: { label: "Open" } },
  initial: "list",
  states: { list: {}, detail: {} },
}).chart({
  offers: { draft: any, open: any },
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
        open: [{ target: "detail" }],
      },
      shows: {
        notesIn: { input: ({ context }) => ({ ids: [context.first, context.second] }) },
        notesNamed: { input: () => ({ prefix: "" }) },
      },
    },
    detail: { shows: { note: { input: ({ context }) => ({ id: context.first }) } } },
  },
});
