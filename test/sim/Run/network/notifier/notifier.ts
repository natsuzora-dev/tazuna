import { service } from "@natsuzora-dev/tazuna";
import { todo } from "../todo/contract.ts";

export const { automation, contract } = service({ description: "Mark each added task seen, and ping todo" });

export const markAddedSeen = automation({
  receives: { taskAdded: todo.taskAdded },
  commands: { markSeen: todo.markSeen },
}).send({ input: ({ payload }) => ({ taskId: payload.taskId }), onRejected: [] });

export const pingOnAdded = automation({ receives: { taskAdded: todo.taskAdded }, commands: { ping: todo.ping } }).send({
  onRejected: [],
});
