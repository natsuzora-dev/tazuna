import { endOf, parseInstant, requested, run, subscriptionOf } from "@natsuzora-dev/tazuna";
import { todo } from "../todo/contract.ts";
import { scenario } from "./data.ts";
import { listScreen } from "./listScreen.ts";

export const showAll = scenario({
  description:
    "Operate showAll; open and its child allTasks both show tasks, and the shows of the innermost state applies, so listScreen ends the subscription with the filter open and subscribes with the filter all",
  given: { start: parseInstant("2026-10-25T10:00:00+09:00"), records: {}, peers: [run(todo, {})] },
  when: (w) => {
    const openSub = w.startup.subscription(todo.tasks);
    const openReached = w.net.deliver(openSub);
    w.net.leaveInFlight(openReached.answer(openReached));
    const showing = w.user.operate(w.startup.screen(listScreen), "showAll");
    w.net.leaveInFlight(showing.end(openSub));
    const allReached = w.net.deliver(showing.subscription(todo.tasks));
    w.net.leaveInFlight(allReached.answer(allReached));
    return { openSub, showing };
  },
  then: ({ openSub, showing }) => [requested(showing, [endOf(openSub), subscriptionOf(todo.tasks, { filter: "all" })])],
});
