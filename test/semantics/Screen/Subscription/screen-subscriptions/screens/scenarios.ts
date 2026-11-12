import { at, mock, operate, scenario } from "@natsuzora-dev/tazuna";
import { todo } from "../todo/contract.ts";
import { listScreen } from "./listScreen.ts";

const tasksShown = mock(listScreen, [todo.tasks, { result: "fulfilled", output: { taskIds: [] } }]);
const countShown = mock(listScreen, [todo.taskCount, { result: "fulfilled", output: { count: 0 } }]);

export const answersOneByOne = scenario(
  "Answer tasks, operate showAll, answer taskCount, and operate showAll; listScreen processes the answers to its subscriptions one at a time as inputs. With only the tasks answer, listScreen is still in loading and does not accept showAll. After the taskCount answer moves it to ready, showAll ends the subscription to tasks and subscribes to tasks again with the changed filter in its input",
  [
    at("2026-10-25T10:00:00+09:00"),
    tasksShown,
    operate(listScreen, "showAll"),
    countShown,
    operate(listScreen, "showAll"),
  ],
);

export const subscriptionsAfterTransitions = scenario(
  "Answer, reload, answer, and peek; listScreen compares its subscriptions with the shows of the state after all transitions of a message. Reloading reenters open, but the input of tasks stays the same, so listScreen does not subscribe again. Peeking passes through peeking, so listScreen does not subscribe to allTasks",
  [
    at("2026-10-25T10:00:00+09:00"),
    tasksShown,
    countShown,
    operate(listScreen, "reload"),
    tasksShown,
    countShown,
    operate(listScreen, "peek"),
  ],
);
