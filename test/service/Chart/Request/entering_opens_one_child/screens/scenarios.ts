import { parseInstant, run } from "@natsuzora-dev/tazuna";
import { todo } from "../todo/contract.ts";
import { given, scenario } from "./data.ts";
import { homeScreen } from "./screens.ts";

const arranged = given({ start: parseInstant("2026-10-25T10:00:00+09:00"), records: {}, peers: [run(todo, {})] });

export const listClosedByParent = scenario({
  description:
    "Open the list at 10:00 and again at 10:02; homeScreen opens one taskListScreen each time it enters listing, and when it exits listing at the one-minute deadline at 10:01, it closes taskListScreen, which ends its subscription to tasks. homeScreen keeps its subscription to taskCount while taskListScreen is open",
  given: arranged,
  when: (w) => {
    const home = w.startup.screen(homeScreen);
    const count = w.net.deliver(w.startup.subscription(todo.taskCount));
    w.net.leaveInFlight(count.answer(count));
    const firstList = w.user.operate(home, "openList").subscription(todo.tasks);
    const first = w.net.deliver(firstList);
    w.net.leaveInFlight(first.answer(first));
    const closing = w.clock.at(parseInstant("2026-10-25T10:02:00+09:00"));
    w.net.leaveInFlight(closing.end(firstList));
    const second = w.net.deliver(w.user.operate(home, "openList").subscription(todo.tasks));
    w.net.leaveInFlight(second.answer(second));
  },
  then: () => [],
});
