import { ref } from "@natsuzora-dev/tazuna";
import { tags } from "../tags/contract.ts";
import { machine, Note } from "./notes.ts";

export const registering = machine({
  description: "Register a note when notes begins, then ask tags for the labels",
  receives: { registered: tags.registered },
  commands: { register: tags.register },
  queries: { labels: tags.labels },
  initial: "asking",
  states: { asking: {}, listing: {}, done: {} },
}).chart({
  on: { registered: [] },
  states: {
    asking: {
      sends: {
        register: {
          input: ({ createKey }) => ({ noteId: createKey(ref(Note)) }),
          onAccepted: [{ target: "listing" }],
          onRejected: [{ target: "done" }],
        },
      },
    },
    listing: {
      calls: { labels: { onFulfilled: [{ target: "done" }], onRejected: [{ target: "done" }] } },
    },
  },
});
