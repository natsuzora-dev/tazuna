import { domain, explore } from "@natsuzora-dev/tazuna";
import { Task } from "./todo.ts";

export const invariantsBreakingCounterExplore = explore({
  service: "invariantsBreakingCounter",
  depth: 2,
  domains: [domain(Task.fields.id, ["task-1"]), domain(Task.fields.title, ["Buy milk"])],
});
