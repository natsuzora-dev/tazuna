import { mkdirSync, rmSync, writeFileSync } from "node:fs";
import { dirname } from "node:path";
import { type DefinitionRef, sameRef } from "../data/definitionRef.ts";
import { type Problem, toProblem } from "../data/problem.ts";
import type { TraceLine } from "../data/trace.generated.ts";
import { toJsonl } from "../data/trace.ts";
import { peerSnapshotName, snapshotEntryPath, snapshotPath } from "../data/traceFile.ts";
import type { Uncovered } from "../data/uncovered.ts";
import { canonicalJson } from "../data/values.ts";
import type { Named, Place } from "../dsl/definition.ts";
import { type Input, type Scenario, timed } from "../dsl/scenario.ts";
import { type Explored, explore } from "../explore/index.ts";
import { seenValues, valuesPerPayload } from "../explore/moves.ts";
import type { Concurrent, Decided, Target } from "../explore/orders.ts";
import { exploreLines, seenLines } from "../explore/paths.ts";
import * as automations from "../explore/uncovered/automations.ts";
import * as charts from "../explore/uncovered/charts.ts";
import * as requests from "../explore/uncovered/requests.ts";
import { comparePlaces, type Found, placeOf, problemOfFound } from "../load/found.ts";
import type { Spec } from "../load/load.ts";
import type { LoadedScenario } from "../load/scenarios.ts";
import { Coverage } from "../sim/spec/coverage.ts";
import { execute, type Run, stepsOf } from "../sim/spec/execute.ts";
import { checkPeers } from "../sim/spec/peers.ts";
import { simulateWithSnapshots } from "../sim/spec/simulate.ts";
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
 * A snapshot that test writes: a scenario's run, or a peer's run of the inputs derived from it (peerSnapshotName).
 * `lines` is undefined for a run that halted.
 */
interface Snapshotted {
  readonly scenario: Pick<Named<unknown>, "service" | "place">;
  readonly name: string;
  readonly lines: readonly TraceLine[] | undefined;
}

/**
 * Compares each run that did not halt with its snapshot, or, with `update`, writes that snapshot and removes the
 * snapshots without a run. Also reports the other violations in the snapshot folders.
 */
function testSnapshots(
  spec: Spec,
  snapshotted: readonly Snapshotted[],
  update: boolean,
): Pick<TestResult, "problems" | "written" | "removed"> {
  const refOf = (s: Snapshotted) => ({ service: s.scenario.service, name: s.name });
  const ended = snapshotted.filter((s) => s.lines !== undefined);
  const linesOf = (s: Snapshotted) => s.lines as readonly TraceLine[];
  const written = update ? ended.map((s) => writeSnapshot(spec, refOf(s), linesOf(s))) : [];
  const { services, folders } = snapshotFolders(spec);
  const scenarios = snapshotted.map((s) => ({ ...refOf(s), compared: s.lines !== undefined }));
  const pairing = pairSnapshots(services, scenarios, folders);
  const problems = update
    ? []
    : ended
        .filter((s) => pairing.compare.some((r) => sameRef(r, refOf(s))))
        .flatMap((s) => snapshotProblems(spec, refOf(s), linesOf(s)));
  const removed: string[] = [];
  for (const p of pairing.problems)
    if (update && p.violation.kind === "Uncomparable.obsoleteSnapshot" && "snapshotEntry" in p.at) {
      const path = snapshotEntryPath(spec, p.at);
      rmSync(path);
      removed.push(path);
    } else if ("scenario" in p.at) {
      const { scenario } = snapshotted.find((s) =>
        sameRef(refOf(s), (p.at as { scenario: DefinitionRef }).scenario),
      ) as Snapshotted;
      problems.push(toProblem(p.violation, scenario.place));
    } else problems.push(pairingProblem(spec, p));
  return { problems, written, removed };
}

/**
 * Runs every scenario and explores it in two phases, checks the mocks that each run that did not halt takes from other
 * spec services (checkPeers), and then tests the snapshots (testSnapshots). Phase 1 collects the
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
  const inputs = new Map<Named<Scenario>, Input[]>(spec.legacyScenarios.map((s) => [s, timed(s.definition)]));
  const runs = new Map<Named<Scenario>, Run>(
    spec.legacyScenarios.map((s) => [s, execute(spec, s.service, inputs.get(s) as Input[])]),
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
  const explored = new Map<Named<Scenario>, Explored>(spec.legacyScenarios.map((s) => [s, exploreOf(s, new Map())]));
  const concurrent = merged(explored.values());
  const paired = new Set([...concurrent.keys()].map((t) => spec.names.get(t)?.service));
  for (const s of spec.legacyScenarios.filter((s) => paired.has(s.service))) explored.set(s, exploreOf(s, concurrent));
  const problems: Problem[] = [];
  const reported = new Set<string>();
  for (const scenario of spec.legacyScenarios) {
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
  const snapshotted: Snapshotted[] = [];
  for (const scenario of spec.legacyScenarios) {
    const run = runs.get(scenario) as Run;
    if (run.halted !== undefined) {
      snapshotted.push({ scenario, name: scenario.name, lines: undefined });
      continue;
    }
    snapshotted.push({ scenario, name: scenario.name, lines: run.outcome.lines });
    for (const check of checkPeers(spec, scenario, run)) {
      problems.push(...check.problems);
      // A peer run without input has no line, so no harness should have to replay an empty file.
      if (check.lines?.length !== 0)
        snapshotted.push({ scenario, name: peerSnapshotName(scenario.name, check.peer), lines: check.lines });
    }
  }
  const simulated = simulateScenarios(spec);
  problems.push(...simulated.problems);
  const seenInLines = seenLines(spec);
  for (const p of simulated.problems) reported.add(canonicalJson([p.kind, p.definition, p.data, p.location]));
  for (const named of spec.scenarios) {
    const explored = exploreLines(spec, named as Named<LoadedScenario>, seenInLines, bounds);
    reached.addAll(explored.reached);
    const ref = { service: named.service, name: named.name };
    for (const { violation, appended } of explored.found) {
      const problem = toProblem(
        violation,
        violation.location ?? (violation.definition === null ? named.place : placeOf(spec, violation.definition)),
        { scenario: ref, appendedLines: appended },
      );
      const key = canonicalJson([problem.kind, problem.definition, problem.data, problem.location]);
      if (reported.has(key)) continue;
      reported.add(key);
      problems.push(problem);
    }
  }
  snapshotted.push(...simulated.snapshotted);
  const snapshots = testSnapshots(spec, snapshotted, options.update);
  return { ...snapshots, problems: [...problems, ...snapshots.problems], reached };
}

/**
 * Simulates each scenario and returns the problems that it reports, each at the line it names, and the trace of each
 * running service when the simulation did not halt: the own service's under the scenario's name, and each running
 * peer's that has lines under peerSnapshotName.
 */
function simulateScenarios(spec: Spec): { readonly problems: Problem[]; readonly snapshotted: Snapshotted[] } {
  const problems: Problem[] = [];
  const snapshotted: Snapshotted[] = [];
  for (const named of spec.scenarios) {
    const { scenario, linePlaces } = named.definition as LoadedScenario;
    const ref = { service: named.service, name: named.name };
    const { world, snapshots } = simulateWithSnapshots(spec, scenario);
    const at = (line: number | null | undefined) =>
      line === null || line === undefined ? undefined : linePlaces[line];
    for (const report of [...world.reports, ...(world.halted === undefined ? [] : [world.halted])]) {
      const line = "scenarioLine" in report.data ? report.data.scenarioLine : undefined;
      problems.push(toProblem(report, at(line) ?? named.place, { scenario: ref }));
    }
    const halted = world.halted !== undefined || [...world.participants.values()].some((p) => p.halted !== undefined);
    for (const [service, p] of world.participants) {
      const violations = [...p.processing.state.violations, ...(p.halted === undefined ? [] : [p.halted])];
      for (const v of violations)
        problems.push(
          toProblem(v, v.location ?? (v.definition === null ? named.place : placeOf(spec, v.definition)), {
            scenario: ref,
          }),
        );
      const lines = snapshots.get(service) ?? [];
      if (service === named.service)
        snapshotted.push({ scenario: named, name: named.name, lines: halted ? undefined : lines });
      else if (lines.length > 0)
        snapshotted.push({
          scenario: named,
          name: peerSnapshotName(named.name, service),
          lines: halted ? undefined : lines,
        });
    }
  }
  return { problems, snapshotted };
}

export const uncoveredOf = (spec: Spec, reached: Coverage): Problem[] =>
  uncoveredChecks
    .flatMap((c) => c.check(spec, reached))
    .sort((x, y) => comparePlaces(x.place, y.place))
    .map(problemOfFound);
