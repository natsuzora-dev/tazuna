import { accepted, answered, fulfilled, parseInstant, rejected } from "@natsuzora-dev/tazuna";
import { addTask, deleteTask, given, myTasks, scenario, User } from "./todo.ts";

const twoUsers = given({
  start: parseInstant("2026-10-25T10:00:00Z"),
  records: { User: [{ id: "u1" }, { id: "u2" }], Task: [] },
  peers: [],
});

export const callerChecks = scenario({
  description:
    "The janitor adds a task, a user with no record adds one, and u1 adds one; todo rejects the first with permission-denied, since addTask lists only users, and the second with not-found, and keeps u1's task as u1's",
  given: twoUsers,
  when: (w) => ({
    byJanitor: w.client.as("janitor").send(addTask, { taskId: "task-1", title: "Sweep" }),
    byGhost: w.client.as(User, "ghost").send(addTask, { taskId: "task-1", title: "Haunt" }),
    byOwner: w.client.as(User, "u1").send(addTask, { taskId: "task-1", title: "Buy milk" }),
    listed: w.client.as(User, "u1").call(myTasks, {}),
  }),
  then: ({ byJanitor, byGhost, byOwner, listed }) => [
    answered(byJanitor, rejected("permission-denied")),
    answered(byGhost, rejected("not-found")),
    answered(byOwner, accepted()),
    answered(listed, fulfilled({ titles: ["Buy milk"] })),
  ],
});

export const ownerOnly = scenario({
  description:
    "u1 adds a task, u2 deletes it, then the janitor deletes it; ownTask rejects u2, who is not the owner, and lets the janitor, a service, delete it",
  given: twoUsers,
  when: (w) => {
    w.client.as(User, "u1").send(addTask, { taskId: "task-1", title: "Buy milk" });
    return {
      byOther: w.client.as(User, "u2").send(deleteTask, { taskId: "task-1" }),
      othersList: w.client.as(User, "u2").call(myTasks, {}),
      byJanitor: w.client.as("janitor").send(deleteTask, { taskId: "task-1" }),
    };
  },
  then: ({ byOther, othersList, byJanitor }) => [
    answered(byOther, rejected("requires", "ownTask")),
    answered(othersList, fulfilled({ titles: [] })),
    answered(byJanitor, accepted()),
  ],
});
