import { guess, scenario } from "./notes.ts";

export const askGuess = scenario(
  "Ask guess, which answers a string of the form of a created Note key that no createKey made, so test reports computedKey",
  {
    given: { start: "2026-10-25T09:00:00+09:00", records: { Note: [] }, peers: {} },
    when: (w) => {
      w.client.call(guess, {});
    },
    then: () => [],
  },
);
