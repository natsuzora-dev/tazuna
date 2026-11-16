import { endOf, requested, run, subscription } from "@natsuzora-dev/tazuna";
import { todo } from "../todo/contract.ts";
import { scenario } from "./data.ts";
import { listScreen } from "./listScreen.ts";

export const showAll = scenario(
  "Operate showAll; open and its child allTasks both show tasks, and the shows of the innermost state applies, so listScreen ends the subscription with the filter open and subscribes with the filter all",
  {
    given: { start: "2026-10-25T10:00:00+09:00", records: {}, peers: { todo: run(todo, {}) } },
    when: (w) => {
      const openSub = w.begin.request(todo.tasks);
      w.net.deliver(openSub);
      w.net.inFlight(openSub);
      const showing = w.user.operate(w.begin.screen(listScreen), "showAll");
      const allSub = showing.request(todo.tasks);
      w.net.deliver(allSub);
      w.net.inFlight(allSub);
      return { openSub, showing };
    },
    then: ({ openSub, showing }) => [requested(showing, [endOf(openSub), subscription(todo.tasks, { filter: "all" })])],
  },
);
