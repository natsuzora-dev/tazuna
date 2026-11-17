import { request, requested, run } from "@natsuzora-dev/tazuna";
import { todo } from "../todo/contract.ts";
import { scenario } from "./data.ts";
import { counterScreen } from "./screens.ts";

const given = { start: "2026-10-25T10:00:00+09:00", records: {}, peers: { todo: run(todo, { Task: [] }) } } as const;

export const staleAnswerRedelivered = scenario(
  "The count answer 0 arrives, then 1, then the network redelivers the answer 0 with its id; screens drops the duplicate, so report sends the count 1",
  {
    given,
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
    then: ({ reporting }) => [requested(reporting, [request(todo.note, { count: 1 })])],
  },
);
