import { instant } from "@natsuzora-dev/tazuna";
import { query } from "./data.ts";

export const nextBusinessDay = query({
  callers: ["todo"],
  input: { after: instant },
  output: { startsAt: instant },
  rejects: ["unavailable"],
  ensures: {
    later: ({ input, output }) => input.after < output.startsAt,
  },
});
