import { device } from "../device/contract.ts";
import { todo } from "../todo/contract.ts";
import { forgetOpenTask, recordNotificationPermission, recordOpenTask } from "./commands.ts";
import { automation } from "./data.ts";

export const recordAddedTask = automation({
  receives: { taskAdded: todo.taskAdded },
  commands: { recordOpenTask },
}).send({
  input: ({ payload }) => ({ taskId: payload.taskId }),
});

export const recordReopenedTask = automation({
  receives: { taskReopened: todo.taskReopened },
  commands: { recordOpenTask },
}).send({
  input: ({ payload }) => ({ taskId: payload.taskId }),
});

export const forgetCompletedTask = automation({
  receives: { taskCompleted: todo.taskCompleted },
  commands: { forgetOpenTask },
}).send({
  input: ({ payload }) => ({ taskId: payload.taskId }),
});

export const forgetDeletedTask = automation({
  receives: { taskDeleted: todo.taskDeleted },
  commands: { forgetOpenTask },
}).send({
  input: ({ payload }) => ({ taskId: payload.taskId }),
});

export const recordGranted = automation({
  receives: { granted: device.notificationPermissionGranted },
  commands: { recordNotificationPermission },
}).send({ input: () => ({ status: "granted" }) });

export const recordDenied = automation({
  receives: { denied: device.notificationPermissionDenied },
  commands: { recordNotificationPermission },
}).send({ input: () => ({ status: "denied" }) });
