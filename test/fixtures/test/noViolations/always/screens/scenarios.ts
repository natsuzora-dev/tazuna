import { fulfilled, parseInstant, run } from "@natsuzora-dev/tazuna";
import { todo } from "../todo/contract.ts";
import { scenario } from "./data.ts";
import { listScreen } from "./listScreen.ts";

export const settlesAfterShownChange = scenario({
  description:
    "Operate leave on listScreen; listScreen enters leaving, and at the end of the macrostep ends its subscription to tasks and sets shown.tasks to null. listScreen evaluates its always guards after the change of shown and enters cleared in the same message, so the operation back takes it to viewing, which subscribes to tasks again",
  given: {
    start: parseInstant("2026-10-25T10:00:00+09:00"),
    records: {},
    peers: [run(todo, { Task: [], Signal: [] })],
  },
  when: (w) => {
    const list = w.startup.screen(listScreen);
    const tasks = w.startup.subscription(todo.tasks);
    w.net.deliver(tasks);
    w.net.deliver(w.peer.todo.answer(tasks, fulfilled({ taskIds: [] })));
    const leaving = w.user.operate(list, "leave");
    w.net.leaveInFlight(leaving.end(tasks));
    w.net.leaveInFlight(w.user.operate(list, "back").subscription(todo.tasks));
  },
  then: () => [],
});
