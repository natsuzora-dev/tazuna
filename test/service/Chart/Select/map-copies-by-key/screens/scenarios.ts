import { type Caused, external, type When } from "@natsuzora-dev/tazuna";
import { todo } from "../todo/contract.ts";
import { scenario } from "./data.ts";
import { listScreen } from "./listScreen.ts";

const given = { start: "2026-10-25T10:00:00+09:00", records: {}, peers: { todo: external(todo) } } as const;
type W = When<typeof given.peers>;

/** The list screen that begin opens, showing todo's answer of `taskIds`. */
const shown = (w: W, ...taskIds: string[]) => {
  w.peer.todo.answer(w.begin.request(todo.tasks), { result: "fulfilled", output: { taskIds } });
  return w.begin.screen(listScreen);
};
const completed = (w: W, line: Caused) => w.peer.todo.answer(line.request(todo.completeTask), { result: "accepted" });
const unanswered = (w: W, ...lines: readonly Caused[]) => {
  for (const line of lines) w.peer.todo.leaveUnanswered(line.request(todo.completeTask));
};

export const routedByKey = scenario(
  "Show task-1 and task-2, complete task-1 twice and task-2 once, and answer; the operation complete reaches only the copy whose key taskId equals the taskId of the payload. The copy of task-1 does not accept a second complete while it waits in completing for the answer. listScreen accepts complete for task-2 while the copy of task-1 waits",
  {
    given,
    when: (w) => {
      const list = shown(w, "task-1", "task-2");
      const first = w.user.operate(list, "complete", { taskId: "task-1" });
      w.user.operate(list, "complete", { taskId: "task-1" });
      const second = w.user.operate(list, "complete", { taskId: "task-2" });
      completed(w, second);
      completed(w, first);
      const third = w.user.operate(list, "complete", { taskId: "task-1" });
      unanswered(w, third);
    },
    then: () => [],
  },
);

export const noCopyForKey = scenario(
  "Show task-1 and complete task-3; the operation complete for task-3, which has no copy, reaches no copy",
  {
    given,
    when: (w) => {
      w.user.operate(shown(w, "task-1"), "complete", { taskId: "task-3" });
    },
    then: () => [],
  },
);

export const withoutKeyFields = scenario(
  "Show two tasks and complete all; the operation completeAll, whose payload has no taskId, reaches every copy",
  {
    given,
    when: (w) => {
      const all = w.user.operate(shown(w, "task-1", "task-2"), "completeAll");
      w.peer.todo.leaveUnanswered(all.request(todo.completeTask, { input: { taskId: "task-1" } }));
      w.peer.todo.leaveUnanswered(all.request(todo.completeTask, { input: { taskId: "task-2" } }));
    },
    then: () => [],
  },
);
