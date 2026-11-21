import { domain, explore } from "@natsuzora-dev/tazuna";
import { recordSteps } from "./todo.ts";

export const todoExplore = explore({ service: "todo", depth: 2, domains: [domain(recordSteps.input.steps, [[]])] });
