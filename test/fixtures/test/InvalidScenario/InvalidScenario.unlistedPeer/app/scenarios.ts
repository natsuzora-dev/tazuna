import { parseInstant } from "@natsuzora-dev/tazuna";
import { scenario } from "./app.ts";

export const noPeers = scenario({
  description: "notifier sends sendMail to mailer, and Given lists no peer",
  given: { start: parseInstant("2026-10-25T09:00:00+09:00"), records: {}, peers: [] },
  when: () => {},
  then: () => [],
});
