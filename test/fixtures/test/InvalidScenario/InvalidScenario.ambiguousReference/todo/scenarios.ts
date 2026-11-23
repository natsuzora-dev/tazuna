import { external, parseInstant } from "@natsuzora-dev/tazuna";
import { mailer } from "../mailer/contract.ts";
import { addTask, scenario } from "./todo.ts";

export const deliverEitherMail = scenario({
  description:
    "Add a task, which mails the owner and the team, and deliver a sendMail that the handle does not tell apart",
  given: { start: parseInstant("2026-10-25T09:00:00+09:00"), records: {}, peers: [external(mailer)] },
  when: (w) => {
    const add = w.client.as("client").send(addTask, { taskId: "task-1" });
    w.net.deliver(add.request(mailer.sendMail));
  },
  then: () => [],
});
