import { emit, service } from "@natsuzora-dev/tazuna";
import { z } from "zod";
import { mailer } from "../mailer/contract.ts";

export const { automation, command, event, contract, scenario } = service({
  name: "todo",
  description: "Keep the tasks and mail the owner and the team about them",
});

export const taskAdded = event({ payload: { taskId: z.string() } });

export const addTask = command({ callers: ["client"], input: { taskId: z.string() }, emits: [taskAdded] }).decide(
  ({ input }) => [emit(taskAdded, { taskId: input.taskId })],
);

export const mailOwner = automation({
  receives: { taskAdded },
  commands: { sendMail: mailer.sendMail },
}).send({ input: () => ({ to: "owner@example.com" }), onRejected: [] });

export const mailTeam = automation({
  receives: { taskAdded },
  commands: { sendMail: mailer.sendMail },
}).send({ input: () => ({ to: "team@example.com" }), onRejected: [] });
