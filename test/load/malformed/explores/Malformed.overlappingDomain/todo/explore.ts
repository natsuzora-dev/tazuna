import { domain, explore, ref } from "@natsuzora-dev/tazuna";
import { Label, Task } from "./todo.ts";

export const todoExplore = explore({
  service: "todo",
  depth: 2,
  domains: [
    domain(Task.fields.id, ["task-1"]),
    domain(Task.fields.title, ["Buy milk"]),
    domain(ref(Task), ["task-2"]),
    domain(Label, [{ text: "Home" }]),
  ],
});
