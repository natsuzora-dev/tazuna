import { parseInstant } from "@natsuzora-dev/tazuna";
import { addTask, scenario, taskTitles } from "./todo.ts";

export const watchTitles = scenario({
  description: "Subscribe to the titles, add two tasks, and ask for the titles; no violation",
  given: { start: parseInstant("2026-10-25T00:00:00Z"), records: { Task: [] }, peers: [] },
  when: (w) => {
    w.client.as("client").subscribe(taskTitles, {});
    w.client.as("client").send(addTask, { taskId: "task-1", title: "Buy milk" });
    w.client.as("client").send(addTask, { taskId: "task-2", title: "Buy eggs" });
    w.client.as("client").call(taskTitles, {});
  },
  then: () => [],
});

export const watchTitlesWrongAnswers = scenario({
  description:
    "Same inputs as watchTitles; the implementation trace of this scenario answers the subscription with other titles, misses an answer, and sends an extra one, so verify reports Mismatch.output, missingAnswer, and unexpectedLine",
  given: { start: parseInstant("2026-10-25T00:00:00Z"), records: { Task: [] }, peers: [] },
  when: (w) => {
    w.client.as("client").subscribe(taskTitles, {});
    w.client.as("client").send(addTask, { taskId: "task-1", title: "Buy milk" });
    w.client.as("client").send(addTask, { taskId: "task-2", title: "Buy eggs" });
    w.client.as("client").call(taskTitles, {});
  },
  then: () => [],
});

export const resubscribeAfterRestart = scenario({
  description:
    "Subscribe to the titles, restart, subscribe again with the same id as a reconnecting client does, and add a task; the restart ended the first subscription, so the new one gets its first answer though it repeats the last answer of the first; no violation",
  given: { start: parseInstant("2026-10-25T00:00:00Z"), records: { Task: [] }, peers: [] },
  when: (w) => {
    const titles = w.client.as("client").subscribe(taskTitles, {});
    w.host.restart();
    w.client.resend(titles);
    w.client.as("client").send(addTask, { taskId: "task-1", title: "Buy milk" });
  },
  then: () => [],
});
