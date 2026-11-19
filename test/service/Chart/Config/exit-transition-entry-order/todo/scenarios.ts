import { addTask, completeTask, given, removeTask, renameTask, scenario } from "./todo.ts";

const arranged = given({ start: "2026-10-25T10:00:00+09:00", records: {}, peers: [] });

export const fromAToB = scenario(
  "Add a task; in the transition from a to b, tracer exits descendants first and enters ancestors first, so it writes to steps in this order: the exit of a1, the exit of a, the assign of the transition, the entry of b, and the entry of b1",
  {
    given: arranged,
    when: (w) => {
      w.client.send(addTask, {});
    },
    then: () => [],
  },
);

export const acrossRegions = scenario(
  "Complete a task; on taskCompleted, regions takes the targetless transition of l1 and the transition of p selected from r1 in one microstep. It exits the states that the two transitions leave, runs the assigns of the transitions in selection order, and then enters the target states, so it writes to steps in this order: the exit of l1, the exit of p, the assign of the transition of l1, the assign of the transition of p, and the entry of q",
  {
    given: arranged,
    when: (w) => {
      w.client.send(completeTask, {});
    },
    then: () => [],
  },
);

export const copyClosedInMicrostep = scenario(
  "Remove a task; on taskRemoved, closer takes the transition from x in right to q and the targetless transition of c1 in the copy k of the map state m in left in one microstep. The transition of x leaves p, so closer first writes to steps the exit of x, the exit of c1, which stops the copy k, and the exit of m. The stopped copy k still takes its transition and adds its assign to seen, without reading the steps that the transition of x writes, because both are in one microstep. closer then writes the assign of the transition of x and the entry of q to steps, and sends seen after steps in recordSteps",
  {
    given: arranged,
    when: (w) => {
      w.client.send(removeTask, {});
    },
    then: () => [],
  },
);

export const intoRegion = scenario(
  "Rename a task; in the transition from idle to l2, a child of the region left of p, opener enters p, enters l2 instead of the initial l1 in left, and enters the initial r1 in the region right, which holds no target. It enters ancestors first and in document order, so it writes to steps in this order: the entry of p, the entry of l2, and the entry of r1",
  {
    given: arranged,
    when: (w) => {
      w.client.send(renameTask, {});
    },
    then: () => [],
  },
);
