import { service } from "@natsuzora-dev/tazuna";
import { mailer } from "../mailer/contract.ts";

export const { machine, scenario } = service({ name: "app", description: "Mail the user" });

export const notifier = machine({
  description: "Mail the user, whose address is not known yet",
  commands: { sendMail: mailer.sendMail },
  initial: "sending",
  states: { sending: {}, done: { type: "final" } },
}).chart({
  states: {
    sending: {
      sends: {
        sendMail: {
          input: () => ({ to: "" }),
          onAccepted: [{ target: "done" }],
          onRejected: [{ target: "done" }],
        },
      },
    },
  },
});
