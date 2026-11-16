import { skip } from "@natsuzora-dev/tazuna";
import { todo } from "../todo/contract.ts";
import { scenario } from "./feed.ts";

export const start = scenario(
  "Start the service; recentScreen shows recent with limit 0, which fails the input schema of recent, so test reports showsInputSchema",
  {
    given: {
      start: "2026-10-25T09:00:00+09:00",
      records: {},
      peers: { todo: skip(todo, "this example is about feed alone") },
    },
    when: (_w) => {},
    then: () => [],
  },
);
