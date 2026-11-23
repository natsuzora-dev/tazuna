import { emit, entity, service } from "@natsuzora-dev/tazuna";
import { z } from "zod";

export const Membership = entity({
  description: "A user's membership of a group",
  fields: { userId: z.string(), groupId: z.string() },
  key: ["userId", "groupId", "userId"],
});

export const { command, createEvent, contract } = service({
  name: "members",
  description: "Keep who belongs to which group",
  entities: { Membership },
});

export const joined = createEvent({ entity: Membership });

export const join = command({
  callers: ["client"],
  input: { userId: Membership.fields.userId, groupId: Membership.fields.groupId },
  emits: [joined],
}).decide(({ input }) => [emit(joined, { userId: input.userId, groupId: input.groupId })]);

export const members = contract({ join });
