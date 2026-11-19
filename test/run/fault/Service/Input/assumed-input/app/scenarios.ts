import { external } from "@natsuzora-dev/tazuna";
import { mailer } from "../mailer/contract.ts";
import { scenario } from "./app.ts";

export const unanswered = scenario(
  "notifier sends sendMail to an empty address, which the input schema of sendMail does not take, and the mailer never answers; the end of the run checks the input of every request to an external service, so test reports inputSchema of notifier also without an answer",
  {
    given: { start: "2026-10-25T09:00:00+09:00", records: {}, peers: [external(mailer)] },
    when: (w) => {
      const sending = w.startup.request(mailer.sendMail);
      w.net.deliver(sending);
      w.peer.mailer.leaveUnanswered(sending);
    },
    then: () => [],
  },
);
