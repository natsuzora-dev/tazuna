import { domain, explore } from "@natsuzora-dev/tazuna";
import { note, starTask } from "./stars.ts";

export const starsExplore = explore({
  service: "stars",
  depth: 2,
  domains: [domain(starTask.input.taskId, ["other-1"]), domain(note.input.taskId, ["other-1"])],
});
