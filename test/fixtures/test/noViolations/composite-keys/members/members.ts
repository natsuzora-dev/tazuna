import { emit, entity, ref, service } from "@natsuzora-dev/tazuna";
import { z } from "zod";

export const User = entity({ description: "A user", fields: { id: z.string() }, key: "id" });
export const Group = entity({ description: "A group", fields: { id: z.string() }, key: "id" });

// A user is a member of a group at most once: the pair of the two ids is the key.
export const Membership = entity({
  description: "A user's membership of a group",
  fields: { userId: ref(User), groupId: ref(Group), role: z.enum(["member", "owner"]) },
  key: ["userId", "groupId"],
});

export const { command, query, createEvent, updateEvent, deleteEvent, contract, given, scenario } = service({
  name: "members",
  description: "Keep who belongs to which group",
  entities: { User, Group, Membership },
});

export const joined = createEvent({ entity: Membership });
export const promoted = updateEvent({ entity: Membership, writes: ["role"] });
export const left = deleteEvent({ entity: Membership });

export const join = command({
  callers: ["client"],
  input: { userId: ref(User), groupId: ref(Group) },
  emits: [joined],
}).decide(({ input }) => [emit(joined, { userId: input.userId, groupId: input.groupId, role: "member" })]);

export const promote = command({
  callers: [Membership],
  input: { membership: ref(Membership) },
  emits: [promoted],
  requires: { byOwner: ({ caller, records }) => records.Membership.get(caller.key)?.role === "owner" },
}).decide(({ refs }) => [
  emit(promoted, { userId: refs.membership.userId, groupId: refs.membership.groupId, role: "owner" }),
]);

export const leave = command({
  callers: ["client"],
  input: { membership: ref(Membership) },
  emits: [left],
}).decide(({ input }) => [emit(left, { userId: input.membership.userId, groupId: input.membership.groupId })]);

export const roleOf = query({
  callers: ["client"],
  input: { userId: ref(User), groupId: ref(Group) },
  output: { role: z.enum(["none", "member", "owner"]) },
}).resolve(({ input, records }) => ({
  role: records.Membership.get({ groupId: input.groupId, userId: input.userId })?.role ?? "none",
}));

export const members = contract({ join, promote, leave, roleOf });
