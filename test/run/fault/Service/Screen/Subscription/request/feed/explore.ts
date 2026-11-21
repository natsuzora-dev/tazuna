import { domain, explore } from "@natsuzora-dev/tazuna";
import { todo } from "../todo/contract.ts";

export const feedExplore = explore({ service: "feed", depth: 2, domains: [domain(todo.recent.output.tasks, [[]])] });
