import { external, parseInstant } from "@natsuzora-dev/tazuna";
import { mailer } from "../mailer/contract.ts";
import { scenario } from "./app.ts";

export const undelivered = scenario({
  description: "notifier sends sendMail at the start, and no line delivers it or leaves it in flight",
  given: { start: parseInstant("2026-10-25T09:00:00+09:00"), records: {}, peers: [external(mailer)] },
  when: () => {},
  then: () => [],
});
