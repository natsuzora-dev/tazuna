import { any, service } from "@natsuzora-dev/tazuna";
import { z } from "zod";

export const { screen } = service({ description: "Pick a task" });

export const listScreen = screen({
  description: "A list that offers a task with an empty id",
  controls: { pick: { label: "Pick", payload: { taskId: z.string().min(1) } } },
  initial: "listing",
  states: { listing: {} },
}).chart({ offers: { pick: () => [{ taskId: "" }] } });

export const filteredScreen = screen({
  description: "A filtered list that offers a task with an empty id",
  controls: { pick: { label: "Pick", payload: { taskId: z.string().min(1) } } },
  initial: "filtered",
  states: { filtered: {} },
}).chart({ offers: { pick: any }, states: { filtered: { offers: { pick: () => [{ taskId: "" }] } } } });
