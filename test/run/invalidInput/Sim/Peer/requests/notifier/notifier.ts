import { service } from "@natsuzora-dev/tazuna";
import { todo } from "../todo/contract.ts";

export const { automation } = service({ description: "Mark the added tasks seen" });

export const markAddedSeen = automation({
  receives: { taskAdded: todo.taskAdded },
  commands: { markSeen: todo.markSeen },
}).send({ input: ({ payload }) => ({ taskId: payload.taskId }), onRejected: [] });
