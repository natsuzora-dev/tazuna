import { emit, entity, service } from "@natsuzora-dev/tazuna";
import { z } from "zod";

export const Membership = entity({
  description: "A user's membership of a group",
  fields: { userId: z.string(), groupId: z.string(), role: z.enum(["member", "owner"]) },
  key: ["userId", "groupId"],
  invariants: { noOwner: ({ record }) => record.role === "member" },
});

export const { command, createEvent, updateEvent, bounds } = service({
  name: "members",
  description: "Keep who belongs to which group",
  entities: { Membership },
});

export const joined = createEvent({ entity: Membership });
export const promoted = updateEvent({ entity: Membership, writes: ["role"] });

export const join = command({
  callers: ["client"],
  input: { userId: Membership.fields.userId, groupId: Membership.fields.groupId },
  emits: [joined],
}).decide(({ input }) => [emit(joined, { userId: input.userId, groupId: input.groupId, role: "member" })]);

// Promoting writes owner, which noOwner forbids.
export const promote = command({
  callers: ["client"],
  input: { userId: Membership.fields.userId, groupId: Membership.fields.groupId },
  emits: [promoted],
}).decide(({ input }) => [emit(promoted, { userId: input.userId, groupId: input.groupId, role: "owner" })]);

export const membersBounds = bounds({ creates: { Membership: 2 } });
