import { domain, explore } from "@natsuzora-dev/tazuna";
import { tagScreen, tagTask } from "./todo.ts";

export const todoExplore = explore({
  service: "todo",
  depth: 2,
  domains: [
    domain(tagTask.input.tags, [["home", "store"]]),
    domain(tagScreen.controls.pick.payload.tags, [["home", "store"]]),
  ],
});
