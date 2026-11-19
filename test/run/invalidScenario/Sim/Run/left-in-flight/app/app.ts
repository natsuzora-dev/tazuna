import { service } from "@natsuzora-dev/tazuna";
import { mailer } from "../mailer/contract.ts";

export const { machine, scenario } = service({ name: "app", description: "Mail the user" });

export const notifier = machine({
  description: "Mail the user, at the start",
  commands: { sendMail: mailer.sendMail },
  initial: "sending",
  states: { sending: {}, done: { type: "final" } },
}).chart({
  states: {
    sending: {
      sends: {
        sendMail: {
          input: () => ({ to: "user@example.com" }),
          onAccepted: [{ target: "done" }],
          onRejected: [{ target: "done" }],
        },
      },
    },
  },
});
