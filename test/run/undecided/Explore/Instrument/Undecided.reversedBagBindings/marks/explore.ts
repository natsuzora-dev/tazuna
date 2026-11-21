import { domain, explore } from "@natsuzora-dev/tazuna";
import { Task, takeMarks } from "./marks.ts";

export const marksExplore = explore({
  service: "marks",
  depth: 2,
  domains: [domain(Task.fields.id, ["task-7"]), domain(takeMarks.input.markIds, [[]])],
});
