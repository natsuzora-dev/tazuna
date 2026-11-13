import { mkdirSync, rmSync, writeFileSync } from "node:fs";
import { dirname } from "node:path";
import { type DefinitionRef, sameRef } from "../data/definitionRef.ts";
import { type Problem, toProblem } from "../data/problem.ts";
import type { TraceLine } from "../data/trace.generated.ts";
import { toJsonl } from "../data/trace.ts";
import { snapshotEntryPath, snapshotPath } from "../data/traceFile.ts";
import type { Uncovered } from "../data/uncovered.ts";
import { canonicalJson } from "../data/values.ts";
import type { Named, Place } from "../dsl/definition.ts";
import { type Input, type Scenario, timed } from "../dsl/scenario.ts";
import { type Explored, explore } from "../explore/index.ts";
import { seenValues, valuesPerPayload } from "../explore/moves.ts";
import type { Concurrent, Decided, Target } from "../explore/orders.ts";
import * as automations from "../explore/uncovered/automations.ts";
import * as charts from "../explore/uncovered/charts.ts";
import * as requests from "../explore/uncovered/requests.ts";
import { comparePlaces, type Found, placeOf, problemOfFound } from "../load/found.ts";
import type { Spec } from "../load/load.ts";
import { Coverage } from "../run/coverage.ts";
import { execute, type Run, stepsOf } from "../run/execute.ts";
import { pairingProblem } from "../verify/pairing.ts";
import { pairSnapshots, snapshotFolders, snapshotProblems } from "../verify/snapshot.ts";

const uncoveredChecks: readonly {
  readonly check: (spec: Spec, reached: Coverage) => readonly Found<Uncovered>[];
}[] = [requests, automations, charts];

export interface TestResult {
  readonly problems: readonly Problem[];
  readonly written: readonly string[];
  readonly removed: readonly string[];
  readonly reached: Coverage;
}

/**
 * Returns the request pairs that the explorations found, each with the sender's place in the first exploration that
 * found it.
 */
function merged(explorations: Iterable<Explored>): Concurrent {
  const all = new Map<Target, Map<Target, Place>>();
  for (const { concurrent } of explorations)
    for (const [first, seconds] of concurrent) {
      const found = all.get(first) ?? new Map<Target, Place>();
      all.set(first, found);
      for (const [second, place] of seconds) if (!found.has(second)) found.set(second, place);
    }
  return all;
}

function writeSnapshot(spec: Spec, scenario: DefinitionRef, lines: readonly TraceLine[]): string {
  const path = snapshotPath(spec, scenario);
  mkdirSync(dirname(path), { recursive: true });
  writeFileSync(path, toJsonl(lines));
  return path;
}

/**
 * Compares the run of each scenario that did not halt with its snapshot, or, with `update`, writes that snapshot and
 * removes the snapshots without a scenario. Also reports the other violations in the snapshot folders.
 */
function testSnapshots(
  spec: Spec,
  runs: ReadonlyMap<Named<Scenario>, Run>,
  update: boolean,
): Pick<TestResult, "problems" | "written" | "removed"> {
  const ended = spec.scenarios.filter((s) => (runs.get(s) as Run).halted === undefined);
  const linesOf = (s: Named<Scenario>) => (runs.get(s) as Run).outcome.lines;
  const written = update ? ended.map((s) => writeSnapshot(spec, s, linesOf(s))) : [];
  const { services, folders } = snapshotFolders(spec);
  const scenarios = spec.scenarios.map((s) => ({ service: s.service, name: s.name, compared: ended.includes(s) }));
  const pairing = pairSnapshots(services, scenarios, folders);
  const problems = update
    ? []
    : ended
        .filter((s) => pairing.compare.some((r) => sameRef(r, s)))
        .flatMap((s) => snapshotProblems(spec, { service: s.service, name: s.name }, linesOf(s)));
  const removed: string[] = [];
  for (const p of pairing.problems)
    if (update && p.violation.kind === "Uncomparable.obsoleteSnapshot" && "snapshotEntry" in p.at) {
      const path = snapshotEntryPath(spec, p.at);
      rmSync(path);
      removed.push(path);
    } else problems.push(pairingProblem(spec, p));
  return { problems, written, removed };
}

/**
 * Runs every scenario and explores it in two phases, and then tests the snapshots (testSnapshots). Phase 1 collects the
 * requests to spec services that a sender sent while another waited. Phase 2 explores again the scenarios of the
 * services those pairs go to, comparing both orders of each pair. Phase 2 explores the same paths as phase 1, so it
 * finds no pair that phase 1 did not find.
 */
export function testSpec(
  spec: Spec,
  options: { readonly update: boolean; readonly depth: number; readonly decided?: Decided },
): TestResult {
  const seen = seenValues(spec);
  const bounds = { depth: options.depth, valuesPerPayload };
  const inputs = new Map<Named<Scenario>, Input[]>(spec.scenarios.map((s) => [s, timed(s.definition)]));
  const runs = new Map<Named<Scenario>, Run>(
    spec.scenarios.map((s) => [s, execute(spec, s.service, inputs.get(s) as Input[])]),
  );
  const reached = new Coverage();
  const exploreOf = (s: Named<Scenario>, concurrent: Concurrent) => {
    const explored = explore(spec, s, inputs.get(s) as Input[], runs.get(s) as Run, {
      seen,
      concurrent,
      bounds,
      decided: options.decided,
    });
    reached.addAll(explored.reached);
    return explored;
  };
  const explored = new Map<Named<Scenario>, Explored>(spec.scenarios.map((s) => [s, exploreOf(s, new Map())]));
  const concurrent = merged(explored.values());
  const paired = new Set([...concurrent.keys()].map((t) => spec.names.get(t)?.service));
  for (const s of spec.scenarios.filter((s) => paired.has(s.service))) explored.set(s, exploreOf(s, concurrent));
  const problems: Problem[] = [];
  const reported = new Set<string>();
  for (const scenario of spec.scenarios) {
    const { found } = explored.get(scenario) as Explored;
    const ref = { service: scenario.service, name: scenario.name };
    for (const { violation, appendedInputs } of found) {
      // Two violations count as one when they differ only in `error`.
      const key = canonicalJson([violation.kind, violation.definition, violation.data, violation.location ?? null]);
      if (reported.has(key)) continue;
      reported.add(key);
      problems.push(
        toProblem(violation, violation.location ?? placeOf(spec, violation.definition), {
          scenario: ref,
          ...(appendedInputs === undefined ? {} : { appendedInputs: stepsOf(spec, scenario.service, appendedInputs) }),
        }),
      );
    }
  }
  const snapshots = testSnapshots(spec, runs, options.update);
  return { ...snapshots, problems: [...problems, ...snapshots.problems], reached };
}

export const uncoveredOf = (spec: Spec, reached: Coverage): Problem[] =>
  uncoveredChecks
    .flatMap((c) => c.check(spec, reached))
    .sort((x, y) => comparePlaces(x.place, y.place))
    .map(problemOfFound);
