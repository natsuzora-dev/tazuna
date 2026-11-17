import type { Json } from "../../data/values.ts";
import { isDescendant } from "../../spec/tree.ts";
import { ref } from "../basic.ts";
import { type Activity, activityRef } from "../chart/basic.ts";
import { openShows, stateEndSubscription } from "../chart/exit.ts";
import type { Processing } from "../chart/queue.ts";
import { Failed, issueViolation } from "../functions.ts";
import { LazyRecordSource } from "../records.ts";
import { awaitAnswer, halt, type Instance, NoteAccess, scopeOf } from "../state.ts";

/**
 * Returns the shows of the active states of `instance` that apply: a state's shows of a slot does not apply while an
 * active descendant shows the same slot, as with offers (innermostOffers). Of two active states in parallel regions
 * that show one slot, the later in document order wins, since refresh sets the slots in this order.
 */
function appliedShows(instance: Instance): (readonly [string, Activity])[] {
  const shows = [...instance.chart.states.values()]
    .filter((st) => instance.entered.has(st.name))
    .flatMap((st) => st.activities.filter((a) => a.keyword === "shows").map((a) => [st.name, a] as const));
  return shows.filter(
    ([n, a]) => !shows.some(([d, b]) => b.key === a.key && d !== n && isDescendant(instance.chart.tree, d, n)),
  );
}

/** Subscribes the shows of `instance` to their current inputs and returns whether the shown value of a slot changed. */
function refresh(r: Processing, instance: Instance): boolean {
  if (instance.closed) return false;
  let shownChanged = false;
  const wanted = new Map<string, { activity: Activity; input: Json; text: string }>();
  const definition = ref(r.st, instance.chart.name);
  for (const [state, activity] of appliedShows(instance)) {
    const slot = activity.key;
    const scope = scopeOf(r.state, instance, state);
    const records = new LazyRecordSource(r.state.records, r.note);
    const input = r.functions.showInput(scope, records, activity, new NoteAccess(r, scope));
    if (input instanceof Failed) return halt(issueViolation(definition, input));
    wanted.set(slot, { activity, input, text: JSON.stringify(input) });
  }
  const open = openShows(r.state, instance.resource);
  for (const p of open) {
    const { slot } = p.requester;
    if (wanted.get(slot)?.text === JSON.stringify(p.input)) continue;
    stateEndSubscription(r, p);
    if (!wanted.has(slot)) {
      r.note.wroteShown(instance.resource, slot);
      shownChanged ||= instance.shown.get(slot) !== null;
      instance.shown.set(slot, null);
    }
  }
  for (const [slot, { activity, input, text }] of wanted) {
    if (open.some((p) => p.requester.slot === slot && JSON.stringify(p.input) === text)) continue;
    awaitAnswer(
      r.state,
      { dir: "out", type: "subscribe", name: activity.target, input },
      { kind: "slot", machine: instance.resource, slot },
      activity,
    );
    r.note.reached({ kind: "request", definition: activityRef(activity), data: {} });
  }
  return shownChanged;
}

/** Returns the resources of the screens whose shown values changed. */
export function refreshScreens(r: Processing): string[] {
  return [...r.state.machines.values()]
    .filter((instance) => instance.chart.screen && refresh(r, instance))
    .map((instance) => instance.resource);
}
