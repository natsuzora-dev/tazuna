import { parseInstant } from "@natsuzora-dev/tazuna";
import { homeScreen } from "./screens.ts";
import { dropTask, given, scenario } from "./todo.ts";

const arranged = given({ start: parseInstant("2026-10-25T10:00:00+09:00"), records: {}, peers: [] });

export const eventAfterClose = scenario({
  description:
    "Open the pick screen and drop a task; homeScreen and pickScreen receive taskDropped, and homeScreen, which opened first, processes it first. homeScreen exits picking and closes pickScreen, so the taskDropped that arrives at pickScreen afterward is dropped",
  given: arranged,
  when: (w) => {
    w.user.operate(w.startup.screen(homeScreen), "openPick");
    w.client.as("client").send(dropTask, {});
  },
  then: () => [],
});
