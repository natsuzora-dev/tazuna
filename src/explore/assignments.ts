import type { Assigned, ChoiceDependent } from "../data/choiceDependent.generated.ts";
import type { DefinitionRef } from "../data/definitionRef.ts";
import { assignmentLimit } from "../data/limits.generated.ts";
import type { Fact, Scenario } from "../data/scenario.generated.ts";
import { canonicalJson, type Json } from "../data/values.ts";
import { type Violation, withExtra } from "../data/violation.ts";
import { placeOf } from "../load/found.ts";
import type { Spec } from "../load/load.ts";
import type { Assignment } from "../sim/network.ts";
import { groupOf, Reported, requestsOf } from "../sim/resolve.ts";
import { expectationLine, expectationNamed, lineNamed } from "../sim/run.ts";
import { executeSpec, type Made } from "../sim/spec/simulate.ts";
import { assignment } from "./choiceDependent.ts";
import { compareOf, outcomeFor } from "./stepOrders.ts";

/** Lean's HandleGroup. */
interface HandleGroup {
  readonly group: Fact;
  readonly target: DefinitionRef;
  readonly line: number;
  readonly handles: number;
}

/** Lean's AssignmentTried. */
interface AssignmentTried {
  readonly assigned: readonly Assigned[];
  readonly found: ChoiceDependent | null;
}

/** Lean's AssignmentSearch. The diff test asks Lean. */
export interface AssignmentSearch {
  readonly tried: readonly AssignmentTried[];
  readonly found: readonly ChoiceDependent[];
}

/** Lean's handleGroups. */
function handleGroups(sc: Scenario): HandleGroup[] {
  const named = [
    ...sc.lines.flatMap((l, i) => lineNamed(l).map((f) => [f, i] as const)),
    ...sc.expectations.flatMap((e) => expectationNamed(e).map((f) => [f, expectationLine(e)] as const)),
  ];
  const groups: HandleGroup[] = [];
  for (const [f, line] of named) {
    if (f.type !== "requests") continue;
    const group = groupOf(f);
    const key = canonicalJson(group as Json);
    const at = groups.findIndex((g) => canonicalJson(g.group as Json) === key);
    const known = groups[at];
    if (known === undefined) groups.push({ group, target: f.target, line, handles: f.handle + 1 });
    else groups[at] = { ...known, handles: Math.max(known.handles, f.handle + 1) };
  }
  return groups;
}

/** Lean's injections. */
function injections(n: number, h: number): number[][] {
  if (h === 0) return [[]];
  return injections(n, h - 1).flatMap((p) =>
    Array.from({ length: n }, (_, x) => x)
      .filter((x) => !p.includes(x))
      .map((x) => [...p, x]),
  );
}

/** Lean's assignmentsOf. */
function assignmentsOf(sized: readonly (readonly [HandleGroup, number])[]): Assignment[][] {
  const [head, ...rest] = sized;
  if (head === undefined) return [[]];
  const [g, size] = head;
  const tails = assignmentsOf(rest);
  return injections(size, g.handles).flatMap((a) => tails.map((t): Assignment[] => [[g.group, a], ...t]));
}

/** Lean's groupSize. */
function groupSize(w: Made["world"], g: HandleGroup): number {
  try {
    return requestsOf(w, g.line, g.group).length;
  } catch (error) {
    if (error instanceof Reported) return 0;
    throw error;
  }
}

/** Lean's assignmentSearch of the handle groups of the scenario `sc`, from its execution with each handle at its own place. */
export function assignmentSearch(spec: Spec, sc: Scenario): AssignmentSearch {
  const groups = handleGroups(sc);
  const [firstGroup] = groups;
  if (firstGroup === undefined) return { tried: [], found: [] };
  const base = executeSpec(spec, sc);
  const sized = groups.map((g) => [g, groupSize(base.world, g)] as const);
  const tried: AssignmentTried[] = [];
  for (const a of assignmentsOf(sized).slice(1)) {
    if (tried.length === assignmentLimit) {
      const limit: ChoiceDependent = {
        kind: "ChoiceDependent.searchLimit",
        definition: firstGroup.target,
        data: { limit: assignmentLimit },
      };
      return { tried, found: [limit] };
    }
    const alternative = executeSpec(spec, sc, [], a);
    const changed = sized.find(([g], k) => canonicalJson(a[k]?.[1] as Json) !== canonicalJson(range(g.handles)));
    const assigned = a.map(
      ([, handles], k): Assigned => ({
        target: (sized[k] as readonly [HandleGroup, number])[0].target,
        handles,
      }),
    );
    const outcomes = [...base.world.services.keys()].map(
      (service) => [service, outcomeFor(base, service), outcomeFor(alternative, service)] as const,
    );
    const found = assignment(
      (service) => compareOf(spec, service),
      (changed?.[0] ?? firstGroup).target,
      assigned,
      outcomes,
    );
    tried.push({ assigned, found: found ?? null });
    if (found !== undefined) return { tried, found: [found] };
  }
  return { tried, found: [] };
}

const range = (n: number): Json => Array.from({ length: n }, (_, i) => i);

/** The violations of assignmentSearch of the scenario `sc`, at the definitions they name. */
export function assignmentChanges(spec: Spec, sc: Scenario): Violation[] {
  return assignmentSearch(spec, sc).found.map((v) => withExtra(v, { location: placeOf(spec, v.definition) }));
}
