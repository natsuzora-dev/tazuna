import { at, from, scenario, send, subscribe } from "@natsuzora-dev/tazuna";
import { board } from "../board/contract.ts";
import { notifier } from "../notifier/contract.ts";
import { addTask, markSeen, tasks } from "./todo.ts";

export const marksSeenForNotifier = scenario(
  "Add a task, and take the command of notifier that marks it seen; notifier sends that command when it receives taskAdded, so test reports nothing and gives notifier the answer",
  [
    at("2026-10-25T10:00:00+09:00"),
    send(addTask, { taskId: "task-1", title: "Buy milk" }),
    from(notifier, send(markSeen, { taskId: "task-1" })),
  ],
);

export const marksOtherTaskSeenForNotifier = scenario(
  "Add a task, and take a command of notifier that marks another task seen; notifier marks only the added task seen, so test reports unproducibleRequest",
  [
    at("2026-10-25T10:00:00+09:00"),
    send(addTask, { taskId: "task-1", title: "Buy milk" }),
    send(addTask, { taskId: "task-2", title: "Buy bread" }),
    from(notifier, send(markSeen, { taskId: "task-1" })),
    from(notifier, send(markSeen, { taskId: "task-3" })),
  ],
);

export const showsTasksToBoard = scenario(
  "Add a task, and take the subscription of board to the tasks; board subscribes when it starts, so test reports nothing and gives board the answers",
  [
    at("2026-10-25T10:00:00+09:00"),
    send(addTask, { taskId: "task-1", title: "Buy milk" }),
    from(board, subscribe(tasks, {})),
    at("2026-10-25T10:01:00+09:00"),
    send(addTask, { taskId: "task-2", title: "Buy bread" }),
  ],
);
