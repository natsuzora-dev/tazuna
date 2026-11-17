import { any, service } from "@natsuzora-dev/tazuna";
import { z } from "zod";

export const { screen, scenario } = service({ name: "screens", description: "Show the tasks" });

export const confirmDialog = screen({
  description: "A dialog that asks whether to clear the list",
  controls: { cancel: { label: "Cancel" } },
  initial: "asking",
  states: { asking: {}, closed: { type: "final" } },
}).chart({ offers: { cancel: any }, states: { asking: { on: { cancel: [{ target: "closed" }] } } } });

export const listScreen = screen({
  description: "A list of two tasks",
  context: { picked: z.string().nullable().default(null) },
  screens: { confirm: confirmDialog },
  controls: {
    pick: { label: "Pick", payload: { taskId: z.string() } },
    clear: { label: "Clear" },
  },
  initial: "listing",
  states: { listing: {}, confirming: {} },
}).chart({
  offers: { clear: any, pick: () => [{ taskId: "task-1" }, { taskId: "task-2" }] },
  states: {
    listing: {
      on: {
        pick: [{ assign: { picked: ({ payload }) => payload.taskId } }],
        clear: [{ target: "confirming" }],
      },
    },
    confirming: { opens: { confirm: { modal: true, onDone: [{ target: "listing" }] } } },
  },
});

export const panel = screen({
  description: "A panel that closes",
  controls: { close: { label: "Close" } },
  initial: "shown",
  states: { shown: {}, closed: { type: "final" } },
}).chart({ offers: { close: any }, states: { shown: { on: { close: [{ target: "closed" }] } } } });

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
