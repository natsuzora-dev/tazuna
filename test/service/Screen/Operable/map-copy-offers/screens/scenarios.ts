import { external, notOffered, offered, type When } from "@natsuzora-dev/tazuna";
import { todo } from "../todo/contract.ts";
import { scenario } from "./data.ts";
import { listScreen } from "./listScreen.ts";

const given = { start: "2026-10-25T10:00:00+09:00", records: {}, peers: { todo: external(todo) } } as const;
type W = When<typeof given.peers>;

const deliveredList = (w: W, ...taskIds: string[]) => {
  const tasks = w.startup.subscription(todo.tasks);
  w.net.deliver(tasks);
  w.net.deliver(w.peer.todo.answer(tasks, { result: "fulfilled", output: { taskIds } }));
  return w.startup.screen(listScreen);
};

export const oneRowNotMarked = scenario(
  "Show task-1 and task-2 and mark task-1; the row of task-2 still offers refresh, because its innermost offering state is row",
  {
    given,
    when: (w) => {
      const list = deliveredList(w, "task-1", "task-2");
      w.user.operate(list, "mark", { taskId: "task-1" });
      return { look: w.user.look(list) };
    },
    then: ({ look }) => [offered(look, "refresh")],
  },
);

export const refreshWhileOneMarked = scenario(
  "Show task-1 and task-2, mark task-1, and refresh; the row of task-2 offers refresh",
  {
    given,
    when: (w) => {
      const list = deliveredList(w, "task-1", "task-2");
      w.user.operate(list, "mark", { taskId: "task-1" });
      w.user.operate(list, "refresh");
    },
    then: () => [],
  },
);

export const onlyRowNotMarked = scenario("Show task-2 alone; its row offers refresh", {
  given,
  when: (w) => ({ look: w.user.look(deliveredList(w, "task-2")) }),
  then: ({ look }) => [offered(look, "refresh")],
});

export const allMarked = scenario("Show task-1 and mark it; no row offers refresh", {
  given,
  when: (w) => {
    const list = deliveredList(w, "task-1");
    w.user.operate(list, "mark", { taskId: "task-1" });
    return { look: w.user.look(list) };
  },
  then: ({ look }) => [notOffered(look, "refresh")],
});
