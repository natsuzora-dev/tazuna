import { itemCount, scenario } from "./summary.ts";

export const countItems = scenario(
  "Count the items; itemCount returns the input field owner, which its output schema does not have, so test reports outputSchema",
  {
    given: { start: "2026-10-25T09:00:00+09:00", records: { Item: [] }, peers: [] },
    when: (w) => {
      w.client.call(itemCount, { owner: "me" });
    },
    then: () => [],
  },
);
