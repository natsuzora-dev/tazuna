import { external, parseInstant } from "@natsuzora-dev/tazuna";
import { mailer } from "../mailer/contract.ts";
import { scenario } from "./app.ts";

export const start = scenario({
  description:
    "scheduler sends scheduleMail with the ISO text of an instant, which the integer schema of its input rejects, so test reports inputSchema of scheduler before the request goes out",
  given: { start: parseInstant("2026-10-25T09:00:00+09:00"), records: {}, peers: [external(mailer)] },
  when: () => {},
  then: () => [],
});
