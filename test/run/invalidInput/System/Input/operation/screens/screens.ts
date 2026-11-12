import { service } from "@natsuzora-dev/tazuna";
import { z } from "zod";

export const { screen } = service({ description: "Show the tasks" });

export const confirmDialog = screen({
  description: "A dialog that asks whether to clear the list",
  controls: { cancel: { label: "Cancel" } },
  initial: "asking",
  states: { asking: {}, closed: { type: "final" } },
}).chart({ states: { asking: { on: { cancel: [{ target: "closed" }] } } } });

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
  offers: { pick: () => [{ taskId: "task-1" }, { taskId: "task-2" }] },
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
