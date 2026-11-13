import { canonicalJson } from "../data/values.ts";
import type { Location, Violation } from "../data/violation.ts";
import type { Named, Place } from "../dsl/definition.ts";
import { type Input, type Scenario, writtenPositions } from "../dsl/scenario.ts";
import type { Spec } from "../load/load.ts";
import { Coverage } from "../run/coverage.ts";
import { execute, extend, type Run } from "../run/execute.ts";
import { type Child, enabledMoves, givable, orderedAfter, type SeenValues } from "./moves.ts";
import { type Concurrent, type Decided, orderChanges, stepOrderChanges, type Target } from "./orders.ts";
import { search } from "./search.ts";

/**
 * The bounds of an exploration. `depth` is the maximum number of inputs appended to a scenario.
 */
export interface Bounds {
  readonly depth: number;
  readonly valuesPerPayload: number;
}

export interface ExploreOptions {
  readonly seen: SeenValues;
  readonly concurrent: Concurrent;
  readonly bounds: Bounds;
  readonly decided?: Decided;
}

interface Found {
  readonly violation: Violation;
  readonly appendedInputs?: readonly Input[];
}

interface ExploredPath {
  readonly appendedInputs: readonly Input[];
}

/**
 * The result of exploring one scenario. `found` holds the violations of the scenario's run and of each path, in the
 * order of the paths. `paths` holds each path that the search reached, breadth-first. `reached` holds what the
 * scenario's run and the paths reached, except runs that halted. `concurrent` holds the requests to spec services that
 * the scenario's run and the paths sent while another request waited.
 */
export interface Explored {
  readonly found: readonly Found[];
  readonly paths: readonly ExploredPath[];
  readonly reached: Coverage;
  readonly concurrent: Concurrent;
}

/**
 * Explores the scenario's run `base` of its timed inputs `prefix`, and the paths that append up to `depth` inputs to
 * it, breadth-first, without extending a path whose state an earlier path reached. Returns the violations of every
 * path; a violation after appended inputs carries them in `appendedInputs`. Also returns the choices and orders that
 * change the result: at each input of the scenario, and after each path that the search extends, among the inputs
 * enabled there and among the steps that each of them takes.
 */
export function explore(
  spec: Spec,
  scenario: Named<Scenario>,
  prefix: readonly Input[],
  base: Run,
  options: ExploreOptions,
): Explored {
  const { service } = scenario;
  const found: Found[] = [];
  const report = (violation: Violation, appendedInputs?: readonly Input[]) =>
    found.push(appendedInputs === undefined ? { violation } : { violation, appendedInputs });
  const concurrent = new Map<Target, Map<Target, Place>>();
  const positions = writtenPositions(scenario.definition);
  // The position of input `k` of a path: as written for the scenario's inputs, and after them for appended inputs.
  const inputAt = (k: number): Location => ({
    file: scenario.place.file,
    line: scenario.place.line,
    input: positions[k] ?? scenario.definition.inputs.length + k - prefix.length + 1,
  });
  const violationsOf = (run: Run, appendedInputs?: readonly Input[]) => {
    // A violation of the run that names no definition and no location is at the input that caused it.
    for (const v of run.outcome.violations) {
      const k = run.inputOf(v);
      report(
        v.definition === null && v.location === undefined && k !== undefined ? { ...v, location: inputAt(k) } : v,
        appendedInputs,
      );
    }
    for (const { first, second, place } of run.requestPairs) {
      const seconds = concurrent.get(first) ?? new Map<Target, Place>();
      concurrent.set(first, seconds);
      if (!seconds.has(second)) seconds.set(second, place);
    }
  };
  violationsOf(base);
  const paths: ExploredPath[] = [];
  const reached = new Coverage();
  if (base.halted !== undefined) return { found, paths, reached, concurrent };
  reached.addAll(base.coverage);

  const changesOptions = (parent: Run, place: Location) => ({
    ordered: orderedAfter(spec, (input) => extend(parent, input)),
    concurrent: options.concurrent,
    step: extend,
    after: (input: Input) => extend(parent, input),
    place,
    decided: options.decided,
  });
  let parent = execute(spec, service, []);
  // A scenario mock names the request it answered in the scenario's run, which the other order also answers.
  const named = (i: number): Input | undefined => {
    const input = prefix[i];
    const to = base.answered[i]?.id;
    return input?.type === "answer" && to !== undefined ? { ...input, choice: { to } } : input;
  };
  for (const [k, input] of prefix.entries()) {
    const withOptions = changesOptions(parent, inputAt(k));
    // The first order fires the first due deadline in each tie, as the scenario's run does.
    const own = withOptions.ordered(named(k) as Input)[0] as Child;
    const next = named(k + 1);
    for (const c of [
      ...orderChanges(spec, service, parent, own, next === undefined ? [] : [next], withOptions),
      ...stepOrderChanges(spec, service, parent, own, withOptions),
    ])
      report(c.violation);
    parent = extend(parent, input);
  }

  const enabled = enabledMoves(spec, service, options.seen, options.bounds.valuesPerPayload);
  const appended = (path: readonly Input[]) => path.slice(prefix.length);
  // Per parent, the children that next built, until the search takes them. A parent's inputs can be the same objects
  // as another parent's, so the parent is part of the key.
  const children = new Map<Run, Map<Input, Run>>();
  const child = (from: Run, input: Input) => {
    const made = children.get(from) as Map<Input, Run>;
    const run = made.get(input) as Run;
    made.delete(input);
    if (made.size === 0) children.delete(from);
    return run;
  };
  // Each enabled input becomes one input per order of the deadlines in its ties. Only the first order of each input is
  // paired with later inputs; changedFork compares its other orders with it.
  const next = (path: readonly Input[], run: Run): Input[] => {
    if (run.halted !== undefined) return [];
    const withOptions = changesOptions(run, inputAt(path.length));
    const ordered = enabled(run)
      .map((input) => withOptions.ordered(input).filter((c) => givable(run, c.result)))
      .filter((c) => c.length > 0);
    const made = new Map(ordered.flat().map((c) => [c.input, c.result] as const));
    for (const own of ordered.flat())
      for (const c of stepOrderChanges(spec, service, run, own, withOptions))
        report(c.violation, [...appended(path), ...c.inputs]);
    const after = (input: Input) => made.get(input) as Run;
    const firsts = ordered.flatMap((c) => c.slice(0, 1));
    // Both orders of a pair append two inputs, so pairs are compared only while both fit within the depth.
    const pairs = appended(path).length + 2 <= options.bounds.depth;
    for (const [i, own] of firsts.entries()) {
      const others = pairs ? firsts.slice(i + 1).map((c) => c.input) : [];
      for (const c of orderChanges(spec, service, run, own, others, { ...withOptions, after }))
        report(c.violation, [...appended(path), ...c.inputs]);
    }
    if (made.size > 0) children.set(run, made);
    return [...made.keys()];
  };
  for (const { path, result, parent: from } of search({
    start: { path: prefix, result: base },
    bound: options.bounds.depth,
    step: child,
    next,
    merge: { fingerprint: (run) => canonicalJson([run.halted !== undefined, run.fingerprint()]) },
  })) {
    if (from === undefined) continue;
    paths.push({ appendedInputs: appended(path) });
    if (result.halted === undefined) reached.addAll(result.coverage);
    violationsOf(result, appended(path));
  }
  return { found, paths, reached, concurrent };
}
