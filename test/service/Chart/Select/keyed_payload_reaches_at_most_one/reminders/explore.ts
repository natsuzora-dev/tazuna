import { domain, explore } from "@natsuzora-dev/tazuna";
import { notify, starTask } from "./reminders.ts";

export const remindersExplore = explore({
  service: "reminders",
  depth: 2,
  domains: [domain(starTask.input.taskId, ["task-1"]), domain(notify.input.taskId, ["task-1"])],
});
