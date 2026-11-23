import { emit, entity, ref, service } from "@natsuzora-dev/tazuna";
import { z } from "zod";

export const User = entity({ description: "A user", fields: { id: z.string() }, key: "id" });
export const Group = entity({ description: "A group", fields: { id: z.string() }, key: "id" });

export const Membership = entity({
  description: "A user's membership of a group",
  fields: { userId: ref(User), groupId: ref(Group) },
  key: ["userId", "groupId"],
});

export const { command, createEvent, deleteEvent, contract, bounds } = service({
  name: "members",
  description: "Keep who belongs to which group",
  entities: { User, Group, Membership },
});

export const userAdded = createEvent({ entity: User });
export const groupAdded = createEvent({ entity: Group });
export const joined = createEvent({ entity: Membership });
export const left = deleteEvent({ entity: Membership });

export const addUser = command({ callers: ["client"], input: { id: User.fields.id }, emits: [userAdded] }).decide(
  ({ input }) => [emit(userAdded, { id: input.id })],
);

export const addGroup = command({ callers: ["client"], input: { id: Group.fields.id }, emits: [groupAdded] }).decide(
  ({ input }) => [emit(groupAdded, { id: input.id })],
);

export const join = command({
  callers: ["client"],
  input: { userId: ref(User), groupId: ref(Group) },
  emits: [joined],
}).decide(({ input }) => [emit(joined, { userId: input.userId, groupId: input.groupId })]);

export const leave = command({
  callers: ["client"],
  input: { userId: Membership.fields.userId, groupId: Membership.fields.groupId },
  emits: [left],
}).decide(({ input }) => [emit(left, { userId: input.userId, groupId: input.groupId })]);

export const members = contract({ addUser, addGroup, join, leave });

export const membersBounds = bounds({ creates: { User: 1, Group: 1, Membership: 1 } });
