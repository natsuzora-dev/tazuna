import { at, cannotOperate, mock, operate, receive, scenario } from "@natsuzora-dev/tazuna";
import { todo } from "../todo/contract.ts";
import { taskDetailScreen } from "./taskDetailScreen.ts";
import { taskListScreen } from "./taskListScreen.ts";

const milk = {
  taskId: "task-1",
  title: "Buy milk",
  dueAt: "2026-10-26T18:00:00+09:00",
  completedAt: null,
};
const completedMilk = { ...milk, completedAt: "2026-10-25T09:00:00+09:00" };
const eggs = { taskId: "task-2", title: "Buy eggs", dueAt: null, completedAt: null };
const milkDetail = {
  title: "Buy milk",
  isCompleted: false,
  dueAt: "2026-10-26T18:00:00+09:00",
  createdAt: "2026-10-25T08:00:00+09:00",
  remindAt: "2026-10-26T18:00:00+09:00",
};

const openList = [
  at("2026-10-25T10:00:00+09:00"),
  mock(taskListScreen, [todo.tasks, { result: "fulfilled", output: { tasks: [milk] } }]),
] as const;
const openDetail = [
  ...openList,
  operate(taskListScreen, "openTask", { taskId: "task-1", title: "Buy milk" }),
  mock(taskDetailScreen, [todo.taskDetail, { result: "fulfilled", output: { task: milkDetail } }]),
] as const;

export const addTask = scenario(
  "Enter a title in the new task field of the list screen and press add; the screen sends addTask",
  [
    ...openList,
    operate(taskListScreen, "add", { title: "Buy eggs" }),
    mock(taskListScreen, [todo.addTask, { result: "accepted" }]),
  ],
);

export const completeAddedTask = scenario(
  "Add a task on the list screen, and press complete on the added task once the list screen shows it; the screen sends completeTask with the key that the screen created for addTask",
  [
    ...openList,
    operate(taskListScreen, "add", { title: "Buy eggs" }),
    mock(taskListScreen, [todo.addTask, { result: "accepted" }]),
    mock(taskListScreen, [
      todo.tasks,
      { result: "fulfilled", output: { tasks: [milk, { ...eggs, taskId: "Task-1" }] } },
    ]),
    operate(taskListScreen, "complete", { taskId: "Task-1" }),
    mock(taskListScreen, [todo.completeTask, { result: "accepted" }]),
  ],
);

export const completeFromList = scenario(
  "Press complete on an open task in the list screen; the screen sends completeTask",
  [
    ...openList,
    operate(taskListScreen, "complete", { taskId: "task-1" }),
    mock(taskListScreen, [todo.completeTask, { result: "accepted" }]),
  ],
);

export const ignoresListOperationsWhileCompleting = scenario(
  "Operate the list screen while completeTask waits for its answer; the screen accepts no complete, reopen, or openTask on any task, no add, and no remindersToggle, and accepts them again after the answer",
  [
    ...openList,
    mock(taskListScreen, [todo.reminderSettings, { result: "fulfilled", output: { shouldRemind: true } }]),
    operate(taskListScreen, "filter", { filter: "all" }),
    mock(taskListScreen, [
      todo.tasks,
      { result: "fulfilled", output: { tasks: [milk, { ...eggs, completedAt: "2026-10-25T09:00:00+09:00" }] } },
    ]),
    operate(taskListScreen, "complete", { taskId: "task-1" }),
    cannotOperate(taskListScreen, "complete", { taskId: "task-1" }),
    cannotOperate(taskListScreen, "reopen", { taskId: "task-2" }),
    cannotOperate(taskListScreen, "openTask", { taskId: "task-2", title: "Buy eggs" }),
    cannotOperate(taskListScreen, "add", { title: "Buy bread" }),
    cannotOperate(taskListScreen, "remindersToggle", { shouldRemind: false }),
    mock(taskListScreen, [todo.completeTask, { result: "accepted" }]),
    operate(taskListScreen, "reopen", { taskId: "task-2" }),
    mock(taskListScreen, [todo.reopenTask, { result: "accepted" }]),
  ],
);

export const reopenFromList = scenario(
  "Choose the completed filter on the list screen, and press reopen on a completed task; the screen sends reopenTask",
  [
    ...openList,
    operate(taskListScreen, "filter", { filter: "completed" }),
    mock(taskListScreen, [todo.tasks, { result: "fulfilled", output: { tasks: [completedMilk] } }]),
    operate(taskListScreen, "reopen", { taskId: "task-1" }),
    mock(taskListScreen, [todo.reopenTask, { result: "accepted" }]),
  ],
);

export const offersCompletionOnList = scenario(
  "Operate the list screen; the screen accepts no reopen on an open task and no complete on a completed task",
  [
    ...openList,
    operate(taskListScreen, "filter", { filter: "all" }),
    mock(taskListScreen, [
      todo.tasks,
      { result: "fulfilled", output: { tasks: [milk, { ...eggs, completedAt: "2026-10-25T09:00:00+09:00" }] } },
    ]),
    cannotOperate(taskListScreen, "reopen", { taskId: "task-1" }),
    cannotOperate(taskListScreen, "complete", { taskId: "task-2" }),
  ],
);

export const keepsFilter = scenario(
  "Choose a filter, and open and close the detail screen; the list screen shows the tasks with the filter chosen before",
  [
    ...openList,
    operate(taskListScreen, "filter", { filter: "all" }),
    mock(taskListScreen, [todo.tasks, { result: "fulfilled", output: { tasks: [milk] } }]),
    operate(taskListScreen, "openTask", { taskId: "task-1", title: "Buy milk" }),
    operate(taskDetailScreen, "close"),
  ],
);

export const completeAndReopenFromDetail = scenario(
  "Press complete on the detail screen, and press reopen while the screen stays open; the screen sends completeTask, then reopenTask",
  [
    ...openDetail,
    operate(taskDetailScreen, "complete"),
    mock(taskDetailScreen, [todo.completeTask, { result: "accepted" }]),
    mock(taskDetailScreen, [
      todo.taskDetail,
      { result: "fulfilled", output: { task: { ...milkDetail, isCompleted: true } } },
    ]),
    operate(taskDetailScreen, "reopen"),
    mock(taskDetailScreen, [todo.reopenTask, { result: "accepted" }]),
  ],
);

export const completedTaskNotCompleted = scenario(
  "Open a completed task on the detail screen; the screen accepts no complete",
  [
    ...openList,
    operate(taskListScreen, "openTask", { taskId: "task-1", title: "Buy milk" }),
    mock(taskDetailScreen, [
      todo.taskDetail,
      { result: "fulfilled", output: { task: { ...milkDetail, isCompleted: true } } },
    ]),
    cannotOperate(taskDetailScreen, "complete"),
  ],
);

export const renameFromDetail = scenario(
  "Finish editing the title field on the detail screen; the screen sends renameTask only if the title changed",
  [
    ...openDetail,
    operate(taskDetailScreen, "rename", { title: "Buy milk" }),
    operate(taskDetailScreen, "rename", { title: "Buy soy milk" }),
    mock(taskDetailScreen, [todo.renameTask, { result: "accepted" }]),
  ],
);

export const keepsOpenWhileRenaming = scenario(
  "Operate the detail screen while renameTask waits for its answer; the screen accepts neither delete nor close, and accepts them again after the answer",
  [
    ...openDetail,
    operate(taskDetailScreen, "rename", { title: "Buy soy milk" }),
    cannotOperate(taskDetailScreen, "delete"),
    cannotOperate(taskDetailScreen, "close"),
    mock(taskDetailScreen, [todo.renameTask, { result: "accepted" }]),
    operate(taskDetailScreen, "close"),
  ],
);

export const changeDueFromDetail = scenario(
  "Choose due dates on the detail screen before and after opening the due row; the screen accepts no dueChoose until the due row opens, sends changeDue only for a time later than now, accepts no operation on the due row and no close while changeDue waits for its answer, and collapses the due row after the answer",
  [
    ...openDetail,
    cannotOperate(taskDetailScreen, "dueChoose", { dueAt: "2026-10-27T18:00:00+09:00" }),
    operate(taskDetailScreen, "dueToggle"),
    operate(taskDetailScreen, "dueChoose", { dueAt: "2026-10-24T18:00:00+09:00" }),
    operate(taskDetailScreen, "dueChoose", { dueAt: "2026-10-27T18:00:00+09:00" }),
    cannotOperate(taskDetailScreen, "dueToggle"),
    cannotOperate(taskDetailScreen, "close"),
    mock(taskDetailScreen, [todo.changeDue, { result: "accepted" }]),
    cannotOperate(taskDetailScreen, "dueClear"),
  ],
);

export const clearDueFromDetail = scenario(
  "Open and collapse the due row on the detail screen without choosing a time, then press dueClear; the screen sends no changeDue on collapse, and changeDue with dueAt null on dueClear",
  [
    ...openDetail,
    operate(taskDetailScreen, "dueToggle"),
    operate(taskDetailScreen, "dueToggle"),
    operate(taskDetailScreen, "dueToggle"),
    operate(taskDetailScreen, "dueClear"),
    mock(taskDetailScreen, [todo.changeDue, { result: "accepted" }]),
  ],
);

export const keepsSameDue = scenario(
  "Choose the task's current due date on the detail screen; the screen collapses the due row without sending changeDue",
  [
    ...openDetail,
    operate(taskDetailScreen, "dueToggle"),
    operate(taskDetailScreen, "dueChoose", { dueAt: "2026-10-26T18:00:00+09:00" }),
    cannotOperate(taskDetailScreen, "dueChoose", { dueAt: "2026-10-27T18:00:00+09:00" }),
  ],
);

export const clearsOnlyDue = scenario(
  "Open a task without a due date on the detail screen; the screen accepts no dueClear",
  [
    ...openList,
    operate(taskListScreen, "openTask", { taskId: "task-1", title: "Buy milk" }),
    mock(taskDetailScreen, [
      todo.taskDetail,
      { result: "fulfilled", output: { task: { ...milkDetail, dueAt: null, remindAt: null } } },
    ]),
    operate(taskDetailScreen, "dueToggle"),
    cannotOperate(taskDetailScreen, "dueClear"),
  ],
);

export const completeWhileDueExpanded = scenario(
  "Press complete while the due row is open on the detail screen; the screen sends completeTask and keeps the due row open",
  [
    ...openDetail,
    operate(taskDetailScreen, "dueToggle"),
    operate(taskDetailScreen, "complete"),
    mock(taskDetailScreen, [todo.completeTask, { result: "accepted" }]),
    operate(taskDetailScreen, "dueClear"),
    mock(taskDetailScreen, [todo.changeDue, { result: "accepted" }]),
  ],
);

export const deleteFromDetail = scenario(
  "Press delete on the detail screen; the screen sends deleteTask without asking the user, accepts no edit and no close while deleteTask waits for its answer, and closes after the answer",
  [
    ...openDetail,
    operate(taskDetailScreen, "delete"),
    cannotOperate(taskDetailScreen, "rename", { title: "Buy soy milk" }),
    cannotOperate(taskDetailScreen, "complete"),
    cannotOperate(taskDetailScreen, "close"),
    mock(taskDetailScreen, [todo.deleteTask, { result: "accepted" }]),
  ],
);

export const closesDeletedTask = scenario("Receive taskDeleted for the task on the detail screen; the screen closes", [
  ...openList,
  operate(taskListScreen, "openTask", { taskId: "task-1", title: "Buy milk" }),
  receive(todo.taskDeleted, { taskId: "task-1" }),
]);

export const changesReminders = scenario(
  "Press remindersToggle on the list screen; the screen sends changeReminders and accepts user operations again after the answer",
  [
    ...openList,
    mock(taskListScreen, [todo.reminderSettings, { result: "fulfilled", output: { shouldRemind: true } }]),
    operate(taskListScreen, "remindersToggle", { shouldRemind: false }),
    mock(taskListScreen, [todo.changeReminders, { result: "accepted" }]),
    operate(taskListScreen, "filter", { filter: "all" }),
  ],
);

export const ignoresListOperationsWhileSending = scenario(
  "Operate the list screen while addTask and changeReminders wait for their answers; the screen accepts no add, remindersToggle, or openTask",
  [
    ...openList,
    mock(taskListScreen, [todo.reminderSettings, { result: "fulfilled", output: { shouldRemind: true } }]),
    operate(taskListScreen, "add", { title: "Buy eggs" }),
    cannotOperate(taskListScreen, "add", { title: "Buy bread" }),
    cannotOperate(taskListScreen, "remindersToggle", { shouldRemind: false }),
    cannotOperate(taskListScreen, "openTask", { taskId: "task-1", title: "Buy milk" }),
    mock(taskListScreen, [todo.addTask, { result: "accepted" }]),
    operate(taskListScreen, "remindersToggle", { shouldRemind: false }),
    cannotOperate(taskListScreen, "add", { title: "Buy bread" }),
    cannotOperate(taskListScreen, "remindersToggle", { shouldRemind: false }),
    cannotOperate(taskListScreen, "openTask", { taskId: "task-1", title: "Buy milk" }),
    mock(taskListScreen, [todo.changeReminders, { result: "accepted" }]),
  ],
);

const unavailable = { result: "rejected", rejection: { kind: "unavailable" } } as const;

export const retriesAfterListRejections = scenario(
  "Let todo reject addTask and changeReminders; the list screen accepts add and remindersToggle again",
  [
    ...openList,
    mock(taskListScreen, [todo.reminderSettings, { result: "fulfilled", output: { shouldRemind: true } }]),
    operate(taskListScreen, "add", { title: "Buy eggs" }),
    mock(taskListScreen, [todo.addTask, unavailable]),
    operate(taskListScreen, "add", { title: "Buy eggs" }),
    mock(taskListScreen, [todo.addTask, { result: "accepted" }]),
    operate(taskListScreen, "remindersToggle", { shouldRemind: false }),
    mock(taskListScreen, [todo.changeReminders, unavailable]),
    operate(taskListScreen, "remindersToggle", { shouldRemind: false }),
    mock(taskListScreen, [todo.changeReminders, { result: "accepted" }]),
  ],
);

export const retriesAfterRowRejections = scenario(
  "Let todo reject completeTask and reopenTask; the list screen accepts complete and reopen on the same task again",
  [
    ...openList,
    operate(taskListScreen, "filter", { filter: "all" }),
    mock(taskListScreen, [
      todo.tasks,
      { result: "fulfilled", output: { tasks: [milk, { ...eggs, completedAt: "2026-10-25T09:00:00+09:00" }] } },
    ]),
    operate(taskListScreen, "complete", { taskId: "task-1" }),
    mock(taskListScreen, [todo.completeTask, unavailable]),
    operate(taskListScreen, "complete", { taskId: "task-1" }),
    mock(taskListScreen, [todo.completeTask, { result: "accepted" }]),
    operate(taskListScreen, "reopen", { taskId: "task-2" }),
    mock(taskListScreen, [todo.reopenTask, unavailable]),
    operate(taskListScreen, "reopen", { taskId: "task-2" }),
    mock(taskListScreen, [todo.reopenTask, { result: "accepted" }]),
  ],
);

export const retriesAfterRenameAndDueRejections = scenario(
  "Let todo reject renameTask and changeDue; the detail screen accepts rename and due date changes again",
  [
    ...openDetail,
    operate(taskDetailScreen, "rename", { title: "Buy soy milk" }),
    mock(taskDetailScreen, [todo.renameTask, unavailable]),
    operate(taskDetailScreen, "rename", { title: "Buy soy milk" }),
    mock(taskDetailScreen, [todo.renameTask, { result: "accepted" }]),
    operate(taskDetailScreen, "dueToggle"),
    operate(taskDetailScreen, "dueChoose", { dueAt: "2026-10-27T18:00:00+09:00" }),
    mock(taskDetailScreen, [todo.changeDue, unavailable]),
    operate(taskDetailScreen, "dueToggle"),
    operate(taskDetailScreen, "dueChoose", { dueAt: "2026-10-27T18:00:00+09:00" }),
    mock(taskDetailScreen, [todo.changeDue, { result: "accepted" }]),
  ],
);

export const retriesAfterCompletionRejections = scenario(
  "Operate the detail screen while completeTask waits for its answer, and let todo reject completeTask and reopenTask; the screen accepts neither complete nor close while waiting, and accepts complete and reopen again after each rejection",
  [
    ...openDetail,
    operate(taskDetailScreen, "complete"),
    cannotOperate(taskDetailScreen, "complete"),
    cannotOperate(taskDetailScreen, "close"),
    mock(taskDetailScreen, [todo.completeTask, unavailable]),
    operate(taskDetailScreen, "complete"),
    mock(taskDetailScreen, [todo.completeTask, { result: "accepted" }]),
    mock(taskDetailScreen, [
      todo.taskDetail,
      { result: "fulfilled", output: { task: { ...milkDetail, isCompleted: true } } },
    ]),
    operate(taskDetailScreen, "reopen"),
    mock(taskDetailScreen, [todo.reopenTask, unavailable]),
    operate(taskDetailScreen, "reopen"),
    mock(taskDetailScreen, [todo.reopenTask, { result: "accepted" }]),
  ],
);

export const keepsEditingAfterDeleteRejected = scenario(
  "Let todo reject deleteTask; the detail screen stays open and accepts operations again",
  [
    ...openDetail,
    operate(taskDetailScreen, "delete"),
    mock(taskDetailScreen, [todo.deleteTask, unavailable]),
    mock(taskDetailScreen, [todo.taskDetail, { result: "fulfilled", output: { task: milkDetail } }]),
    operate(taskDetailScreen, "complete"),
    mock(taskDetailScreen, [todo.completeTask, { result: "accepted" }]),
  ],
);

export const keepsDetailWhenOtherTaskDeleted = scenario(
  "Receive taskDeleted for another task while the detail screen is open; the screen stays open",
  [
    ...openDetail,
    receive(todo.taskDeleted, { taskId: "task-2" }),
    operate(taskDetailScreen, "complete"),
    mock(taskDetailScreen, [todo.completeTask, { result: "accepted" }]),
  ],
);

export const openTaskNotReopened = scenario("Open an open task on the detail screen; the screen accepts no reopen", [
  ...openDetail,
  cannotOperate(taskDetailScreen, "reopen"),
]);
