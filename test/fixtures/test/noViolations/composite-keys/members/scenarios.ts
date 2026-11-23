import { accepted, answered, fulfilled, parseInstant, rejected } from "@natsuzora-dev/tazuna";
import { given, join, leave, Membership, promote, roleOf, scenario } from "./members.ts";

const ann = given({
  start: parseInstant("2026-11-23T10:00:00Z"),
  records: {
    User: [{ id: "ann" }, { id: "bob" }],
    Group: [{ id: "chess" }],
    Membership: [{ userId: "ann", groupId: "chess", role: "owner" }],
  },
  peers: [],
});

export const joinOnce = scenario({
  description:
    "bob joins chess twice; the second join is rejected with already-exists, since the pair of user and group is the key",
  given: ann,
  when: (w) => ({
    first: w.client.as("client").send(join, { userId: "bob", groupId: "chess" }),
    second: w.client.as("client").send(join, { userId: "bob", groupId: "chess" }),
    role: w.client.as("client").call(roleOf, { userId: "bob", groupId: "chess" }),
  }),
  then: ({ first, second, role }) => [
    answered(first, accepted()),
    answered(second, rejected("already-exists")),
    answered(role, fulfilled({ role: "member" })),
  ],
});

export const ownerPromotes = scenario({
  description:
    "bob joins chess, bob tries to promote himself, then ann, the owner, promotes him; the caller is a membership, named by its key",
  given: ann,
  when: (w) => {
    w.client.as("client").send(join, { userId: "bob", groupId: "chess" });
    return {
      bySelf: w.client
        .as(Membership, { userId: "bob", groupId: "chess" })
        .send(promote, { membership: { userId: "bob", groupId: "chess" } }),
      byOwner: w.client
        .as(Membership, { groupId: "chess", userId: "ann" })
        .send(promote, { membership: { groupId: "chess", userId: "bob" } }),
      role: w.client.as("client").call(roleOf, { userId: "bob", groupId: "chess" }),
    };
  },
  then: ({ bySelf, byOwner, role }) => [
    answered(bySelf, rejected("requires", "byOwner")),
    answered(byOwner, accepted()),
    answered(role, fulfilled({ role: "owner" })),
  ],
});

export const leaveTwice = scenario({
  description: "ann leaves chess twice; the second leave is rejected with not-found, since no membership has that key",
  given: ann,
  when: (w) => ({
    first: w.client.as("client").send(leave, { membership: { userId: "ann", groupId: "chess" } }),
    second: w.client.as("client").send(leave, { membership: { userId: "ann", groupId: "chess" } }),
    role: w.client.as("client").call(roleOf, { userId: "ann", groupId: "chess" }),
  }),
  then: ({ first, second, role }) => [
    answered(first, accepted()),
    answered(second, rejected("not-found")),
    answered(role, fulfilled({ role: "none" })),
  ],
});
