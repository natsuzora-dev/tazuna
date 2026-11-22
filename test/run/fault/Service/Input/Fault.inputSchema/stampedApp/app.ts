import { service } from "@natsuzora-dev/tazuna";
import { mailer } from "../mailer/contract.ts";

export const { machine, scenario } = service({ name: "stampedApp", description: "Schedule a mail" });

const at: number = JSON.parse('"2026-10-25T00:00:00Z"');

export const scheduler = machine({
  description: "Schedule a mail at a time that it holds as the ISO text of an instant",
  commands: { scheduleMail: mailer.scheduleMail },
  initial: "scheduling",
  states: { scheduling: {}, done: { type: "final" } },
}).chart({
  states: {
    scheduling: {
      sends: {
        scheduleMail: {
          input: () => ({ at }),
          onAccepted: [{ target: "done" }],
          onRejected: [{ target: "done" }],
        },
      },
    },
  },
});
