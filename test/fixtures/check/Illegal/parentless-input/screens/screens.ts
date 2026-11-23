import { service } from "@natsuzora-dev/tazuna";
import { z } from "zod";

export const { screen } = service({ name: "screens", description: "Show the tasks" });

export const taskScreen = screen({
  description: "One task",
  input: { taskId: z.string() },
  initial: "showing",
  states: { showing: {} },
}).chart({});
