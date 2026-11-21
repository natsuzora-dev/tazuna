import { domain, explore } from "@natsuzora-dev/tazuna";
import { announce } from "./notifier.ts";

export const notifierExplore = explore({
  service: "notifier",
  depth: 2,
  domains: [domain(announce.input.taskId, ["task-1"])],
});
