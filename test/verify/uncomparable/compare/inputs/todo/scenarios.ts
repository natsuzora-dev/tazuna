import { external, fulfilled } from "@natsuzora-dev/tazuna";
import { calendar } from "../calendar/contract.ts";
import { addTask, given, scenario } from "./todo.ts";

const arranged = given({
  start: "2026-10-25T00:00:00Z",
  records: { Task: [] },
  peers: [external(calendar)],
});

export const addOne = scenario("Add one task; the trace has a second input, so verify reports unexpectedInput", {
  given: arranged,
  when: (w) => {
    w.net.leaveInFlight(w.client.send(addTask, { taskId: "task-1", title: "Buy milk" }).request(calendar.nextDay));
  },
  then: () => [],
});

export const addTwo = scenario("Add two tasks; the trace lacks the second input, so verify reports missingInput", {
  given: arranged,
  when: (w) => {
    w.net.leaveInFlight(w.client.send(addTask, { taskId: "task-1", title: "Buy milk" }).request(calendar.nextDay));
    w.net.leaveInFlight(w.client.send(addTask, { taskId: "task-2", title: "Buy eggs" }).request(calendar.nextDay));
  },
  then: () => [],
});

export const addMilk = scenario(
  "Add a task to buy milk; the trace's input adds a task to buy eggs, so verify reports differentInput",
  {
    given: arranged,
    when: (w) => {
      w.net.leaveInFlight(w.client.send(addTask, { taskId: "task-1", title: "Buy milk" }).request(calendar.nextDay));
    },
    then: () => [],
  },
);

export const answerDay = scenario(
  "Add a task and answer the next day; the trace's answer input answers a request that the implementation did not send, so verify reports differentInput",
  {
    given: arranged,
    when: (w) => {
      const day = w.client.send(addTask, { taskId: "task-1", title: "Buy milk" }).request(calendar.nextDay);
      w.net.deliver(day);
      w.net.deliver(w.peer.calendar.answer(day, fulfilled({ day: "2026-10-26T00:00:00Z" })));
    },
    then: () => [],
  },
);
