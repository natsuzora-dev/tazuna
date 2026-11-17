import type { TraceLine } from "@natsuzora-dev/tazuna/view";

/** The label colors, each a `.t-<tone>` rule of style.css. */
export const tones = [
  "event",
  "control",
  "command",
  "query",
  "answer",
  "screen",
  "after",
  "always",
  "onDone",
  "operation",
  "restart",
] as const;

export type Tone = (typeof tones)[number];

export const lineTones: Readonly<Record<TraceLine["type"], Tone>> = {
  event: "event",
  command: "command",
  query: "query",
  subscribe: "query",
  unsubscribe: "query",
  answer: "answer",
  operation: "operation",
  restart: "restart",
  time: "after",
};
