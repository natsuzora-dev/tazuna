import { domain, explore } from "@natsuzora-dev/tazuna";
import { logTitle } from "./todo.ts";

export const todoExplore = explore({ service: "todo", depth: 2, domains: [domain(logTitle.input.title, [""])] });
