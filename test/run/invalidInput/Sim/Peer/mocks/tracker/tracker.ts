import { service } from "@natsuzora-dev/tazuna";
import { todo } from "../todo/contract.ts";

export const { automation } = service({ description: "Complete each task that todo reports completed" });

export const completeReported = automation({
  receives: { taskCompleted: todo.taskCompleted },
  commands: { completeTask: todo.completeTask },
}).send({ input: ({ payload }) => ({ taskId: payload.taskId }), onRejected: [] });
