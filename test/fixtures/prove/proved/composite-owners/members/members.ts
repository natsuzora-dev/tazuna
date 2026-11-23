import { emit, entity, ref, service } from "@natsuzora-dev/tazuna";
import { z } from "zod";

export const Membership = entity({
  description: "A user's membership of a group",
  fields: { userId: z.string(), groupId: z.string(), role: z.enum(["member", "owner"]) },
  key: ["userId", "groupId"],
});

export const { command, createEvent, updateEvent, bounds } = service({
  name: "members",
  description: "Keep who belongs to which group",
  entities: { Membership },
  invariants: {
    oneOwnerPerGroup: ({ records }) =>
      records.Membership.every(
        (m) =>
          m.role === "member" ||
          records.Membership.filter((o) => o.groupId === m.groupId && o.role === "owner").size === 1,
      ),
  },
});

export const joined = createEvent({ entity: Membership });
export const promoted = updateEvent({ entity: Membership, writes: ["role"] });

export const join = command({
  callers: ["client"],
  input: { userId: Membership.fields.userId, groupId: Membership.fields.groupId },
  emits: [joined],
}).decide(({ input }) => [emit(joined, { userId: input.userId, groupId: input.groupId, role: "member" })]);

// The membership is a key object; refs reads its record, and the group may have no owner yet.
export const promote = command({
  callers: ["client"],
  input: { membership: ref(Membership) },
  requires: {
    member: ({ refs }) => refs.membership.role === "member",
    noOwnerYet: ({ input, records }) =>
      records.Membership.every((o) => o.groupId !== input.membership.groupId || o.role === "member"),
  },
  emits: [promoted],
}).decide(({ input }) => [
  emit(promoted, { userId: input.membership.userId, groupId: input.membership.groupId, role: "owner" }),
]);

export const membersBounds = bounds({ creates: { Membership: 2 } });
