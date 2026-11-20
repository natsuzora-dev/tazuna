import { service } from "@natsuzora-dev/tazuna";
import { todo } from "../todo/contract.ts";

export const { automation, contract, machine } = service({
  name: "notifier",
  description: "Mark each added task seen, ping todo, and follow todo's notes",
});

export const markAddedSeen = automation({
  receives: { taskAdded: todo.taskAdded },
  commands: { markSeen: todo.markSeen },
}).send({ input: ({ payload }) => ({ taskId: payload.taskId }), onRejected: [] });

export const pingOnAdded = automation({ receives: { taskAdded: todo.taskAdded }, commands: { ping: todo.ping } }).send({
  onRejected: [],
});

export const following = machine({
  description: "Take todo's notes",
  receives: { noted: todo.noted },
  initial: "following",
  states: { following: {} },
}).chart({
  states: { following: { on: { noted: [{ target: "following" }] } } },
});
