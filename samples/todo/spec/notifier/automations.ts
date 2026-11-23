import { device } from "../device/contract.ts";
import { todo } from "../todo/contract.ts";
import { recordPermissionChoice, recordTaskChange } from "./commands.ts";
import { automation } from "./data.ts";

export const recordAddedTask = automation({
  receives: { taskAdded: todo.taskAdded },
  commands: { recordTaskChange },
}).send({
  input: ({ payload }) => ({ taskId: payload.taskId, at: payload.at, change: "opened" }),
});

export const recordReopenedTask = automation({
  receives: { taskReopened: todo.taskReopened },
  commands: { recordTaskChange },
}).send({
  input: ({ payload }) => ({ taskId: payload.taskId, at: payload.at, change: "opened" }),
});

export const recordCompletedTask = automation({
  receives: { taskCompleted: todo.taskCompleted },
  commands: { recordTaskChange },
}).send({
  input: ({ payload }) => ({ taskId: payload.taskId, at: payload.at, change: "closed" }),
});

export const recordDeletedTask = automation({
  receives: { taskDeleted: todo.taskDeleted },
  commands: { recordTaskChange },
}).send({
  input: ({ payload }) => ({ taskId: payload.taskId, at: payload.at, change: "closed" }),
});

export const recordGranted = automation({
  receives: { granted: device.notificationPermissionGranted },
  commands: { recordPermissionChoice },
}).send({ input: ({ payload }) => ({ status: "granted", at: payload.at }) });

export const recordDenied = automation({
  receives: { denied: device.notificationPermissionDenied },
  commands: { recordPermissionChoice },
}).send({ input: ({ payload }) => ({ status: "denied", at: payload.at }) });
