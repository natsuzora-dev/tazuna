import { any, service } from "@natsuzora-dev/tazuna";
import { z } from "zod";

export const { screen, contract } = service({ name: "screens", description: "Show the tasks" });

export const pickScreen = screen({
  description: "Pick a title, writing constant offers as functions, methods, and parenthesized arrays",
  controls: { close: { label: "Close" }, pick: { label: "Pick", payload: { title: z.string() } } },
  initial: "open",
  states: { open: {}, picked: {}, done: {} },
}).chart({
  offers: { close: () => [{}], pick: () => [] },
  states: {
    open: {
      offers: { close: any, pick: () => [{ title: "Buy milk" }] },
      on: { pick: [{ target: "picked" }], close: [{ target: "done" }] },
    },
    picked: {
      offers: {
        close: () => [],
        pick: ({ now }) => (now > 0 ? [{ title: "Buy bread" }] : []),
      },
    },
    done: {
      offers: {
        close() {
          return [];
        },
        pick: () => [],
      },
    },
  },
});

export const screens = contract({});
