import { ref } from "../basic.ts";
import { limits } from "../limits.ts";
import { stateValueName } from "../note.ts";
import { type Chosen, copiesOf, type Instance, machine, ownerOf, report } from "../state.ts";
import { transitionsAt } from "./basic.ts";
import { syncCopies } from "./map.ts";
import { microstep } from "./microstep.ts";
import type { Processing } from "./queue.ts";
import { leavesOf, select } from "./select.ts";

/**
 * Evaluates the always transitions of the owner of `name` (a copy's owner for a copy). It reuses a cached evaluation
 * only while no guard holds; after any transition, even one that writes nothing, it re-evaluates.
 */
export function settle(r: Processing, name: string, step: number): void {
  const owner = machine(r.state, ownerOf(r.state, name));
  if (owner === undefined) return;
  const { evaluations } = r;
  const rounds = { count: 0 };
  for (;;) {
    if (owner.closed) return;
    const changed = syncCopies(r, owner, step);
    let chosen: Chosen[] = [];
    if (!evaluations.replayIfFresh(owner.resource, "always")) {
      const reads = evaluations.track(() => {
        chosen = select(
          r,
          owner,
          ["always"],
          {},
          leavesOf(r, owner, () => true),
        );
      });
      // Watch every state with always transitions and every map state too, so a change of the active states or the copy
      // set triggers re-evaluation.
      const states = [owner, ...copiesOf(r.state, owner)].flatMap((holder) =>
        [...owner.chart.states.values()]
          .filter((state) => transitionsAt(owner.chart, state.name, ["always"]).length > 0 || state.kind === "map")
          .map((state) => stateValueName(holder.resource, state.name)),
      );
      // After a transition the evaluation stays stale, so only one that chose nothing is remembered.
      if (chosen.length === 0) evaluations.remember(owner.resource, "always", reads, [...reads, ...states]);
    }
    if (chosen.length === 0 && !changed) return;
    countRound(r, owner, rounds);
    if (chosen.length > 0) microstep(r, owner, chosen, {}, step);
  }
}

function countRound(r: Processing, instance: Instance, rounds: { count: number }): void {
  if (rounds.count === limits.alwaysRounds)
    report(r.state, {
      kind: "Fault.exceededAlwaysRounds",
      definition: ref(r.st, instance.chart.name),
      data: { limit: limits.alwaysRounds },
    });
  rounds.count += 1;
}

/**
 * Runs `work` between two settles of the owner of `name`; without an instance, as for an automation's answer, only runs
 * it.
 */
export function settled(r: Processing, name: string | undefined, step: number, work: () => void): void {
  if (name === undefined) {
    work();
    return;
  }
  const owner = ownerOf(r.state, name);
  r.note.settlesAround(owner);
  settle(r, owner, step);
  work();
  settle(r, owner, step);
}
