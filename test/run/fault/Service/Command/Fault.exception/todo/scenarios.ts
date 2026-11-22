import { parseInstant } from "@natsuzora-dev/tazuna";
import { logTitle, scenario } from "./todo.ts";

export const logEmpty = scenario({
  description:
    "Log an empty title; the refinement of the payload schema of titleLogged throws, so test reports exception of titleLogged",
  given: { start: parseInstant("2026-10-25T09:00:00+09:00"), records: {}, peers: [] },
  when: (w) => {
    w.client.send(logTitle, { title: "" });
  },
  then: () => [],
});
