import { at, call, scenario, send } from "@natsuzora-dev/tazuna";
import { addTask, taskCount } from "./todo.ts";

export const resent = scenario(
  "Send addTask twice with the id c1 and the same input; todo does not process the second and answers it again with the first answer",
  [
    at("2026-10-25T09:00:00+09:00"),
    send(addTask, { taskId: "task-1", title: "Buy milk" }, { id: "c1" }),
    send(addTask, { taskId: "task-1", title: "Buy milk" }, { id: "c1" }),
  ],
);

export const changedInput = scenario(
  "Send addTask with the id c1, again with another input, and again with the first input; todo rejects the second with reused-id and answers the third again with the first answer",
  [
    at("2026-10-25T09:00:00+09:00"),
    send(addTask, { taskId: "task-1", title: "Buy milk" }, { id: "c1" }),
    send(addTask, { taskId: "task-1", title: "Buy eggs" }, { id: "c1" }),
    send(addTask, { taskId: "task-1", title: "Buy milk" }, { id: "c1" }),
  ],
);

export const correctedInput = scenario(
  "Send addTask with the id c1 and an input that does not fit the schema, then with the input fixed; todo rejects the first with invalid-input and does not keep the rejection as the answer of c1, so it processes the second",
  [
    at("2026-10-25T09:00:00+09:00"),
    send(addTask, { taskId: "task-1", title: "" }, { id: "c1" }),
    send(addTask, { taskId: "task-1", title: "Buy milk" }, { id: "c1" }),
  ],
);

export const askedTwice = scenario(
  "Ask for taskCount with the id q1, add a task, and ask again with q1; todo processes both queries and answers the second with the count after addTask",
  [
    at("2026-10-25T09:00:00+09:00"),
    call(taskCount, {}, { id: "q1" }),
    send(addTask, { taskId: "task-1", title: "Buy milk" }),
    call(taskCount, {}, { id: "q1" }),
  ],
);
