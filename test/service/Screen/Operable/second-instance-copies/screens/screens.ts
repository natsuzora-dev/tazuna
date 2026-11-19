import { any, service } from "@natsuzora-dev/tazuna";
import { z } from "zod";

export const { screen, given, scenario } = service({ name: "screens", description: "Count per row in panels" });

export const panel = screen({
  description: "A panel whose rows each count the bumps of their key",
  controls: { bump: { label: "Bump", payload: { row: z.string() } }, close: { label: "Close" } },
  initial: "shown",
  states: {
    shown: {
      initial: "rows",
      states: {
        rows: {
          type: "map",
          key: { row: z.string() },
          context: { bumps: z.number().default(0) },
          initial: "counting",
          states: { counting: {} },
        },
      },
    },
    closed: { type: "final" },
  },
}).chart({
  offers: { bump: () => [{ row: "a" }, { row: "b" }], close: any },
  states: {
    shown: { on: { close: [{ target: "closed" }] } },
    rows: { items: () => [{ row: "a" }, { row: "b" }] },
    counting: {
      on: {
        bump: [
          {
            guard: { ownRow: ({ key, payload }) => key.row === payload.row },
            assign: { bumps: ({ context }) => context.bumps + 1 },
          },
        ],
      },
    },
  },
});

export const board = screen({
  description: "A board whose two regions each open a panel",
  screens: { panel },
  controls: { openLeft: { label: "Open left" }, openRight: { label: "Open right" } },
  initial: "regions",
  states: {
    regions: {
      type: "parallel",
      states: {
        left: { initial: "leftIdle", states: { leftIdle: {}, leftOpen: {} } },
        right: { initial: "rightIdle", states: { rightIdle: {}, rightOpen: {} } },
      },
    },
  },
}).chart({
  offers: { openLeft: any, openRight: any },
  states: {
    leftIdle: { on: { openLeft: [{ target: "leftOpen" }] } },
    leftOpen: { opens: { panel: { modal: false, onDone: [{ target: "leftIdle" }] } } },
    rightIdle: { on: { openRight: [{ target: "rightOpen" }] } },
    rightOpen: { opens: { panel: { modal: false, onDone: [{ target: "rightIdle" }] } } },
  },
});
