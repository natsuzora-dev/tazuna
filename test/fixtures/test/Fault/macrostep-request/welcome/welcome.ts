import { emit, service } from "@natsuzora-dev/tazuna";
import { z } from "zod";

export const { automation, command, event, contract, scenario } = service({
  name: "welcome",
  description: "Welcome the members",
});

export const joined = event({ payload: { nickname: z.string() } });
export const greeted = event({ payload: { name: z.string() } });

export const join = command({ callers: ["client"], input: { nickname: z.string() }, emits: [joined] }).decide(
  ({ input }) => [emit(joined, { nickname: input.nickname })],
);

export const greet = command({
  callers: ["client", "welcome"],
  input: { name: z.string().min(1) },
  emits: [greeted],
}).decide(({ input }) => [emit(greeted, { name: input.name })]);

export const greetJoined = automation({
  receives: { joined },
  commands: { greet },
}).send({ input: ({ payload }) => ({ name: payload.nickname }) });
