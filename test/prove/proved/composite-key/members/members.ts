import { emit, entity, ref, service } from "@natsuzora-dev/tazuna";
import { z } from "zod";

export const User = entity({ description: "A user", fields: { id: z.string() }, key: "id" });
export const Group = entity({ description: "A group", fields: { id: z.string() }, key: "id" });

export const Membership = entity({
  description: "A user's membership of a group",
  fields: { userId: ref(User), groupId: ref(Group) },
  key: ["userId", "groupId"],
});

export const { command, createEvent, bounds } = service({
  name: "members",
  description: "Keep who belongs to which group",
  entities: { User, Group, Membership },
});

export const joined = createEvent({ entity: Membership });

// The ref inputs exist, or the command rejects with not-found, so a membership's user and group never dangle.
export const join = command({
  callers: ["client"],
  input: { userId: ref(User), groupId: ref(Group) },
  emits: [joined],
}).decide(({ input }) => [emit(joined, { userId: input.userId, groupId: input.groupId })]);

export const membersBounds = bounds({ creates: { User: 1, Group: 1, Membership: 2 } });
