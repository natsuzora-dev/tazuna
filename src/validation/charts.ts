import type { Illegal } from "../data/illegal.generated.ts";
import type { Structure } from "../spec/structure.generated.ts";
import { type ChartStructure, isOpenedByScreen, stateNamed, type TransitionStructure } from "../spec/structure.ts";
import { addEntrySet, domainDepth, enterable, entryOrder, historyTargets, kindOf, pathOf } from "../spec/tree.ts";

function parentKeys(chart: ChartStructure): string[] {
  return (["input", "requires", "output", "ensures"] as const).filter((key) => chart[key].length > 0);
}

function missingParents(structure: Structure): Illegal[] {
  return structure.definitions.flatMap((d): Illegal[] => {
    if (d.kind !== "screen" || isOpenedByScreen(structure, d)) return [];
    const keys = parentKeys(d);
    return keys.length === 0
      ? []
      : [{ kind: "Illegal.missingParent", definition: { service: d.service, name: d.name }, data: { keys } }];
  });
}

function unlistedControls(structure: Structure): Illegal[] {
  return structure.definitions.flatMap((d) =>
    d.kind !== "machine" && d.kind !== "screen"
      ? []
      : Object.keys(d.controls).flatMap((control): Illegal[] =>
          Object.hasOwn(d.offers, control)
            ? []
            : [
                {
                  kind: "Illegal.unlistedControl",
                  definition: { service: d.service, name: d.name },
                  data: { control },
                },
              ],
        ),
  );
}

function ownQueries(structure: Structure): Illegal[] {
  return structure.definitions.flatMap((d) =>
    d.kind !== "machine" && d.kind !== "screen"
      ? []
      : Object.entries(d.queries).flatMap(([key, q]): Illegal[] =>
          q === null || q.service !== d.service
            ? []
            : [{ kind: "Illegal.ownQuery", definition: { service: d.service, name: d.name }, data: { key } }],
        ),
  );
}

/**
 * Returns the states whose always transitions are re-evaluated after `t`, in document order. For a history target,
 * every state it may restore counts as entered: its targets without a record, and every child a record may hold (a map
 * state's record is empty, since only copies enter its children).
 */
function lands(chart: ChartStructure, source: string, t: TransitionStructure): string[] {
  if (t.target === null) return [source];
  const common = domainDepth(chart, source, t.target, t.reenter === true);
  const target = stateNamed(chart, t.target);
  const parent = target?.parent ?? null;
  const recordable =
    target?.kind === "history" && parent !== null && kindOf(chart, parent) !== "map" ? enterable(chart, parent) : [];
  const entering = new Set<string>();
  const candidates = [...historyTargets(chart, chart.initial, new Map(), t.target), ...recordable];
  for (const c of candidates) addEntrySet(chart, new Set(), common, c, entering);
  if (target?.kind !== "history" && pathOf(chart, t.target).length <= common) entering.add(t.target);
  if (pathOf(chart, source).length <= common) entering.add(source);
  return entryOrder(chart, entering);
}

interface Edge {
  readonly from: string;
  readonly lands: readonly string[];
  readonly guarded: boolean;
}

function edges(chart: ChartStructure): Edge[] {
  return chart.states.flatMap((state) =>
    state.transitions
      .filter((t) => t.trigger.type === "always")
      .map((t) => ({ from: state.name, lands: lands(chart, state.name, t), guarded: t.guards.length > 0 })),
  );
}

type Predecessors = readonly (readonly [string, string])[];

/** The BFS queue and the predecessor of each found state. */
interface Frontier {
  readonly queue: readonly string[];
  readonly predecessors: Predecessors;
}

function visit(f: Frontier, to: string, from: string): Frontier {
  return f.predecessors.some(([found]) => found === to)
    ? f
    : { queue: [...f.queue, to], predecessors: [...f.predecessors, [to, from]] };
}

function visitAll(s: string, f: Frontier, lands: readonly string[]): Frontier {
  return lands.reduce((frontier, to) => visit(frontier, to, s), f);
}

type Search = { readonly kind: "cycle"; readonly predecessors: Predecessors } | { readonly kind: "none" };

function expand(es: readonly Edge[], s: string, f: Frontier): Frontier {
  return es.filter((e) => e.from === s).reduce((frontier, e) => visitAll(s, frontier, e.lands), f);
}

function search(es: readonly Edge[], start: string, f: Frontier): Search {
  let frontier = f;
  for (;;) {
    const [s, ...rest] = frontier.queue;
    if (s === undefined) return { kind: "none" };
    if (s === start) return { kind: "cycle", predecessors: frontier.predecessors };
    frontier = expand(es, s, { queue: rest, predecessors: frontier.predecessors });
  }
}

/** Returns the path from `start` back to `start` through predecessors. */
function pathBack(start: string, predecessors: Predecessors, s: string, path: readonly string[]): string[] {
  const p = predecessors.find(([found]) => found === s)?.[1];
  if (p === undefined || p === start) return [start, ...path];
  return pathBack(
    start,
    predecessors.filter(([found]) => found !== s),
    p,
    [p, ...path],
  );
}

function searchFrom(es: readonly Edge[], e: Edge): Search {
  return search(es, e.from, visitAll(e.from, { queue: [], predecessors: [] }, e.lands));
}

/**
 * Returns the path of the first unguarded always transition that leads back to its state. Only cycles that start with
 * an unguarded always transition count: a cycle of guarded ones may stop on guard values, so `test` catches it with the
 * always-round limit.
 */
function cyclePath(chart: ChartStructure): string[] | null {
  const es = edges(chart);
  for (const e of es.filter((edge) => !edge.guarded)) {
    const found = searchFrom(es, e);
    if (found.kind === "cycle") return pathBack(e.from, found.predecessors, e.from, [e.from]);
  }
  return null;
}

function alwaysCycles(structure: Structure): Illegal[] {
  return structure.definitions.flatMap((d): Illegal[] => {
    if (d.kind !== "machine" && d.kind !== "screen") return [];
    const path = cyclePath(d);
    return path === null
      ? []
      : [{ kind: "Illegal.alwaysCycle", definition: { service: d.service, name: d.name }, data: { statePath: path } }];
  });
}

export function check(structure: Structure): Illegal[] {
  return [
    ...missingParents(structure),
    ...ownQueries(structure),
    ...unlistedControls(structure),
    ...alwaysCycles(structure),
  ];
}
