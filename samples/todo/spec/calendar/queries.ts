import { date } from "@natsuzora-dev/tazuna";
import { query } from "./data.ts";

export const nextBusinessDay = query({
  input: { from: date },
  output: { day: date },
  rejects: ["unavailable"],
  ensures: {
    afterFrom: ({ input, output }) => Temporal.PlainDate.compare(input.from, output.day) < 0,
  },
});
