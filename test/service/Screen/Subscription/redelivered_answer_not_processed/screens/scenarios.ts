import { parseInstant, requested, requestOf, run } from "@natsuzora-dev/tazuna";
import { todo } from "../todo/contract.ts";
import { given, scenario } from "./data.ts";
import { counterScreen } from "./screens.ts";

const arranged = given({
  start: parseInstant("2026-10-25T10:00:00+09:00"),
  records: {},
  peers: [run(todo, { Task: [] })],
});

export const staleAnswerRedelivered = scenario({
  description:
    "The count answer 0 arrives, then 1, then the network redelivers the answer 0 with its id; screens drops the duplicate, so report sends the count 1",
  given: arranged,
  when: (w) => {
    const screen = w.startup.screen(counterScreen);
    const sub = w.startup.subscription(todo.taskCount);
    const reached = w.net.deliver(sub);
    const zero = reached.answer(reached);
    w.net.deliver(zero);
    const adding = w.client.send(todo.addTask, { taskId: "t1" });
    const one = adding.answer(reached);
    w.net.deliver(one);
    w.net.redeliver(zero);
    const reporting = w.user.operate(screen, "report");
    w.net.leaveInFlight(reporting.request(todo.note));
    return { reporting };
  },
  then: ({ reporting }) => [requested(reporting, [requestOf(todo.note, { count: 1 })])],
});
