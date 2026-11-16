import { at, from, scenario, send, subscribe, unsubscribe } from "@natsuzora-dev/tazuna";
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

const watchedByBoard = subscribe(tasks, {});

export const endsBoardSubscriptionWithBoard = scenario(
  "Take the subscription of board to the tasks, add the task close, and take board's end of the subscription; board ends it when it closes on taskAdded of close, so test reports nothing",
  [
    at("2026-10-25T10:00:00+09:00"),
    from(board, watchedByBoard),
    send(addTask, { taskId: "close", title: "Close the board" }),
    from(board, unsubscribe(watchedByBoard)),
  ],
);

export const endsBoardSubscriptionBeforeBoard = scenario(
  "Take the subscription of board to the tasks and board's end of it while board stays open; board does not end it, so test reports unproducibleRequest",
  [at("2026-10-25T10:00:00+09:00"), from(board, watchedByBoard), from(board, unsubscribe(watchedByBoard))],
);

export const answersBoardAfterItCloses = scenario(
  "Take the subscription of board to the tasks, add the task close, and add another task without ending the subscription; board gets the new answer to the subscription that it ended as a late answer and ignores it, so test reports nothing",
  [
    at("2026-10-25T10:00:00+09:00"),
    from(board, watchedByBoard),
    send(addTask, { taskId: "close", title: "Close the board" }),
    at("2026-10-25T10:01:00+09:00"),
    send(addTask, { taskId: "task-1", title: "Buy milk" }),
  ],
);
