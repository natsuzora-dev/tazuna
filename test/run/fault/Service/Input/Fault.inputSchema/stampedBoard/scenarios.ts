import { run } from "@natsuzora-dev/tazuna";
import { dueTasks } from "../dueTasks/tasks.ts";
import { scenario } from "./board.ts";

export const show = scenario({
  description:
    "board shows dueBy with the text of an Instant, which the datetime codec of its input does not encode, so test reports inputSchema of board",
  given: { start: "2026-10-25T09:00:00+09:00", records: {}, peers: [run(dueTasks, {})] },
  when: () => {},
  then: () => [],
});
