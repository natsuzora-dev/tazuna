import { external, notOffered } from "@natsuzora-dev/tazuna";
import { todo } from "../todo/contract.ts";
import { scenario } from "./data.ts";
import { rowScreen } from "./rowScreen.ts";

export const offersPerCopy = scenario(
  "Show task-1 and task-2 and complete them; rowScreen evaluates offers per copy. While the copies of task-1 and task-2 are in idle, it accepts complete for both taskIds. When the copy of task-1 enters completing, its offers return [], so rowScreen does not accept complete for task-1 but still accepts it for task-2",
  {
    given: { start: "2026-10-25T10:00:00+09:00", records: {}, peers: { todo: external(todo) } },
    when: (w) => {
      const rows = w.begin.screen(rowScreen);
      const openTasks = w.begin.subscription(todo.openTasks);
      w.net.deliver(openTasks);
      w.net.deliver(
        w.peer.todo.answer(openTasks, {
          result: "fulfilled",
          output: { taskIds: ["task-1", "task-2"] },
        }),
      );
      const first = w.user.operate(rows, "complete", { taskId: "task-1" }).request(todo.completeTask);
      const look = w.user.look(rows);
      const second = w.user.operate(rows, "complete", { taskId: "task-2" }).request(todo.completeTask);
      w.net.deliver(first);
      w.peer.todo.leaveUnanswered(first);
      w.net.deliver(second);
      w.peer.todo.leaveUnanswered(second);
      return { look };
    },
    then: ({ look }) => [notOffered(look, "complete", { taskId: "task-1" })],
  },
);
