import { service } from "@natsuzora-dev/tazuna";
import { z } from "zod";

export const { screen } = service({ name: "screens", description: "Pick a task" });

export const pickerScreen = screen({
  description: "A picker, which no screen opens, so no screen reads its output",
  output: { taskId: z.string() },
  initial: "picking",
  states: { picking: {}, picked: { type: "final" } },
  ensures: { picked: ({ output }) => output.taskId !== "" },
}).chart({ resolve: () => ({ taskId: "task-1" }) });
