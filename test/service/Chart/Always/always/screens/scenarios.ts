import { fulfilled, run } from "@natsuzora-dev/tazuna";
import { todo } from "../todo/contract.ts";
import { scenario } from "./data.ts";
import { listScreen } from "./listScreen.ts";

export const settlesAfterShownChange = scenario(
  "Operate leave on listScreen; listScreen enters leaving, and at the end of the macrostep ends its subscription to tasks and sets shown.tasks to null. listScreen evaluates its always guards after the change of shown and enters cleared in the same message, so it is not in leaving when the message is processed",
  {
    given: {
      start: "2026-10-25T10:00:00+09:00",
      records: {},
      peers: { todo: run(todo, { Task: [], Signal: [] }) },
    },
    when: (w) => {
      const list = w.startup.screen(listScreen);
      const tasks = w.startup.subscription(todo.tasks);
      w.net.deliver(tasks);
      w.net.deliver(w.peer.todo.answer(tasks, fulfilled({ taskIds: [] })));
      const leaving = w.user.operate(list, "leave");
      w.net.leaveInFlight(leaving.end(tasks));
    },
    then: () => [],
  },
);
