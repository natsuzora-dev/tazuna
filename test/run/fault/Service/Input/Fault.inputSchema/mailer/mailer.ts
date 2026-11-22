import { externalService, instant } from "@natsuzora-dev/tazuna";
import { z } from "zod";

export const { command, contract } = externalService({ name: "mailer", description: "Send mails" });

export const sendMail = command({
  input: { to: z.string().min(1) },
  emits: [],
  rejects: ["invalid-input", "unavailable", "reused-id"],
});

export const scheduleMail = command({
  input: { at: instant },
  emits: [],
  rejects: ["invalid-input", "unavailable", "reused-id"],
});
