import { external, fulfilled } from "@natsuzora-dev/tazuna";
import { calendar } from "../calendar/contract.ts";
import { addDoneTask, addTask, completeTask, given, scenario } from "./todo.ts";

const arranged = given({ start: "2026-10-25T10:00:00+09:00", records: {}, peers: [external(calendar)] });
const nextDay = fulfilled({ day: "2026-10-26T00:00:00+09:00" });

export const answerAfterExit = scenario(
  "Add a task, complete it, answer, add another task, and answer; dayNoter sends calendar.nextDay each time it enters asking. The answer to the first request arrives after completeTask has made dayNoter exit asking, so it takes no transition. The answer to the second request moves dayNoter to noting, which records the next day",
  {
    given: arranged,
    when: (w) => {
      const first = w.client.send(addTask, { taskId: "task-1" }).request(calendar.nextDay);
      w.net.deliver(first);
      w.client.send(completeTask, { taskId: "task-1" });
      w.net.deliver(w.peer.calendar.answer(first, nextDay));
      const second = w.client.send(addTask, { taskId: "task-2" }).request(calendar.nextDay);
      w.net.deliver(second);
      w.net.deliver(w.peer.calendar.answer(second, nextDay));
    },
    then: () => [],
  },
);

export const passThrough = scenario(
  "Add a done task; in the one message of addDoneTask, dayNoter enters asking on taskAdded and exits it on taskCompleted. It is not in asking at the end of the macrostep, so it sends no calendar.nextDay",
  {
    given: arranged,
    when: (w) => {
      w.client.send(addDoneTask, { taskId: "task-1" });
    },
    then: () => [],
  },
);
