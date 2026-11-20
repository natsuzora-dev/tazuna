import { accepted, external, fulfilled, type ProcessingLine } from "@natsuzora-dev/tazuna";
import { todo } from "../todo/contract.ts";
import { given, scenario } from "./data.ts";
import { taskScreen } from "./taskScreen.ts";

const arranged = given({ start: "2026-10-25T10:00:00+09:00", records: {}, peers: [external(todo)] });

const deliverTaskSubscription = arranged.step((w) => w.net.deliver(w.startup.subscription(todo.task)));
const deliverShown = arranged.step((w, isCompleted: boolean) =>
  w.net.deliver(w.peer.todo.answer(w.startup.subscription(todo.task), fulfilled({ isCompleted }))),
);
const deliverAccepted = arranged.step((w, line: ProcessingLine) => {
  const complete = line.request(todo.completeTask);
  w.net.deliver(complete);
  w.net.deliver(w.peer.todo.answer(complete, accepted()));
});

export const acceptedWithoutTransition = scenario({
  description:
    "Show an open task and operate complete twice; the offers of complete of root return [{}] while taskScreen waits for the answer to completeTask, so taskScreen accepts complete, but completing has no transition on complete, so it sends no second completeTask",
  given: arranged,
  when: (w) => {
    const task = w.startup.screen(taskScreen);
    deliverTaskSubscription(w);
    deliverShown(w, false);
    const first = w.user.operate(task, "complete");
    w.user.operate(task, "complete");
    deliverAccepted(w, first);
  },
  then: () => [],
});
