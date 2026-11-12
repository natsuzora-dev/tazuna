import { exitSet } from "../../syntax/tree.ts";
import type { Instance } from "../state.ts";
import type { Chart, Transition } from "./basic.ts";

export function exitsOf(instance: Instance, t: Pick<Transition, "source" | "target" | "reenter">): string[] {
  if (t.target === null) return [];
  return exitSet(instance.chart.tree, instance.entered, t.source, t.target, t.reenter);
}

export function slots(c: Chart): string[] {
  return [
    ...new Set(
      [...c.states.values()].flatMap((st) => st.activities.filter((a) => a.keyword === "shows").map((a) => a.key)),
    ),
  ];
}
