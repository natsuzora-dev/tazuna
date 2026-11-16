import { external } from "@natsuzora-dev/tazuna";
import { calendar } from "../calendar/contract.ts";
import { addDoneTask, addTask, completeTask, scenario } from "./todo.ts";

const given = { start: "2026-10-25T10:00:00+09:00", records: {}, peers: { calendar: external(calendar) } } as const;
const nextDay = { result: "fulfilled", output: { day: "2026-10-26T00:00:00+09:00" } } as const;

export const answerAfterExit = scenario(
  "Add a task, complete it, answer, add another task, and answer; dayNoter sends calendar.nextDay each time it enters asking. The answer to the first request arrives after completeTask has made dayNoter exit asking, so it takes no transition. The answer to the second request moves dayNoter to noting, which records the next day",
  {
    given,
    when: (w) => {
      const first = w.client.send(addTask, { taskId: "task-1" });
      w.client.send(completeTask, { taskId: "task-1" });
      w.peer.calendar.answer(first.request(calendar.nextDay), nextDay);
      const second = w.client.send(addTask, { taskId: "task-2" });
      w.peer.calendar.answer(second.request(calendar.nextDay), nextDay);
    },
    then: () => [],
  },
);

export const passThrough = scenario(
  "Add a done task; in the one message of addDoneTask, dayNoter enters asking on taskAdded and exits it on taskCompleted. It is not in asking at the end of the macrostep, so it sends no calendar.nextDay",
  {
    given,
    when: (w) => {
      w.client.send(addDoneTask, { taskId: "task-1" });
    },
    then: () => [],
  },
);
