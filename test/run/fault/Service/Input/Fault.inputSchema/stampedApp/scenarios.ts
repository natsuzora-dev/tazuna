import { external } from "@natsuzora-dev/tazuna";
import { mailer } from "../mailer/contract.ts";
import { scenario } from "./app.ts";

export const start = scenario({
  description:
    "scheduler sends scheduleMail with the text of an Instant, which the datetime codec of its input does not encode, so test reports inputSchema of scheduler before the request goes out",
  given: { start: "2026-10-25T09:00:00+09:00", records: {}, peers: [external(mailer)] },
  when: () => {},
  then: () => [],
});
