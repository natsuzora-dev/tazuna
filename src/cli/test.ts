import { mkdirSync, rmSync, writeFileSync } from "node:fs";
import { dirname } from "node:path";
import type { CheckedSpec } from "../check/spec.ts";
import type { TraceLine } from "../data/trace.generated.ts";
import { toJsonl } from "../data/trace.ts";
import { type Run, sameRun, snapshotEntryPath, snapshotPath } from "../data/traceFile.ts";
import { canonicalJson } from "../data/values.ts";
import { type ReportedViolation, toReported } from "../data/violation.ts";
import type { Named } from "../dsl/definition.ts";
import { exploreLines } from "../explore/paths.ts";
import { stepOrderChanges } from "../explore/stepOrders.ts";
import { uncoveredParts } from "../explore/uncovered.ts";
import { comparePlaces, placeOf, reportedOfFound } from "../load/found.ts";
import type { Spec } from "../load/load.ts";
import type { LoadedScenario } from "../load/scenarios.ts";
import { Coverage } from "../sim/spec/coverage.ts";
import { serviceViolations, simulateSpec, snapshotsOf } from "../sim/spec/simulate.ts";
import { snapshotPairingViolation } from "../verify/pairing.ts";
import { pairSnapshots, snapshotFolders, snapshotViolations } from "../verify/snapshot.ts";

export interface TestResult {
  readonly violations: readonly ReportedViolation[];
  readonly written: readonly string[];
  readonly removed: readonly string[];
  readonly reached: Coverage;
  /** How many worlds the search after each scenario visited. */
  readonly visited: readonly number[];
}

function writeSnapshot(spec: Spec, run: Run, lines: readonly TraceLine[]): string {
  const path = snapshotPath(spec, run);
  mkdirSync(dirname(path), { recursive: true });
  writeFileSync(path, toJsonl(lines));
  return path;
}

/** A run that test snapshots. `lines` is undefined for a run that halted. */
interface Snapshotted {
  readonly run: Run;
  readonly lines: readonly TraceLine[] | undefined;
}

/**
 * Compares each run that did not halt with its snapshot, or, with `update`, writes that snapshot and removes the
 * snapshots without a run, and reports the other violations in the snapshot folders. It leaves as they are the entries
 * named after a scenario that `skipped` holds: `<scenario>`, or `<scenario>.<anything>`.
 */
function testSnapshots(
  spec: Spec,
  snapshotted: readonly Snapshotted[],
  update: boolean,
  skipped: readonly Named<LoadedScenario>[],
): Pick<TestResult, "violations" | "written" | "removed"> {
  const ofSkipped = (service: string, entry: string) =>
    skipped.some((s) => s.service === service && (entry === s.name || entry.startsWith(`${s.name}.`)));
  const ended = snapshotted.flatMap(({ run, lines }) => (lines === undefined ? [] : [{ run, lines }]));
  const written = update ? ended.map((s) => writeSnapshot(spec, s.run, s.lines)) : [];
  const { services, folders } = snapshotFolders(spec);
  const pairing = pairSnapshots(
    services,
    snapshotted.map((s) => ({ run: s.run, compared: s.lines !== undefined })),
    folders,
  );
  const violations = [
    ...(update
      ? []
      : ended
          .filter((s) => pairing.compare.some((r) => sameRun(r, s.run)))
          .flatMap((s) => snapshotViolations(spec, s.run, s.lines))),
  ];
  const removed: string[] = [];
  for (const p of pairing.violations)
    if (p.at.kind === "snapshotEntry" && ofSkipped(p.at.service, p.at.entry)) continue;
    else if (update && p.violation.kind === "Uncomparable.obsoleteSnapshot" && p.at.kind === "snapshotEntry") {
      const path = snapshotEntryPath(spec, p.at.service, p.at.entry);
      rmSync(path);
      removed.push(path);
    } else violations.push(snapshotPairingViolation(spec, p));
  return { violations, written, removed };
}

/**
 * Simulates and explores `scenarios`, some or all of the spec's, then tests the snapshots (testSnapshots). A scenario
 * still written as an input list, which only verify's examples keep, is not run, and its snapshot is kept.
 */
export function testSpec(
  spec: CheckedSpec,
  options: { readonly update: boolean; readonly scenarios: readonly Named<LoadedScenario>[] },
): TestResult {
  const { scenarios } = options;
  const reached = new Coverage();
  const simulated = simulateScenarios(spec, scenarios);
  const violations: ReportedViolation[] = [];
  const reported = new Set<string>();
  // Two violations count as one when they differ only in `error`.
  const report = (violation: ReportedViolation) => {
    const key = canonicalJson([violation.kind, violation.definition, violation.data, violation.location]);
    if (reported.has(key)) return;
    reported.add(key);
    violations.push(violation);
  };
  for (const violation of simulated.violations) report(violation);
  const visited: number[] = [];
  for (const named of scenarios) {
    const explored = exploreLines(spec, named);
    reached.addAll(explored.reached);
    visited.push(explored.visited);
    const ref = { service: named.service, name: named.name };
    for (const { violation, appended } of explored.found)
      report(
        toReported(
          violation,
          violation.location ?? (violation.definition === null ? named.place : placeOf(spec, violation.definition)),
          { scenario: ref, appendedLines: appended },
        ),
      );
  }
  const skipped = spec.scenarios.filter((s) => !scenarios.includes(s));
  const snapshots = testSnapshots(spec, simulated.snapshotted, options.update, skipped);
  return { ...snapshots, violations: [...violations, ...snapshots.violations], reached, visited };
}

/**
 * Simulates each of `scenarios` and returns the violations that it reports, each at the line it names, with the step orders
 * that change the result of one of its processings, and the trace of each running service when the simulation did not
 * halt: the own service's, and each running peer's that has lines.
 */
function simulateScenarios(
  spec: Spec,
  scenarios: readonly Named<LoadedScenario>[],
): {
  readonly violations: ReportedViolation[];
  readonly snapshotted: Snapshotted[];
} {
  const violations: ReportedViolation[] = [];
  const snapshotted: Snapshotted[] = [];
  for (const named of scenarios) {
    const { scenario, linePlaces, expectationPlaces } = named.definition;
    const ref = { service: named.service, name: named.name };
    const simulated = simulateSpec(spec, scenario);
    const { world } = simulated;
    const snapshots = snapshotsOf(simulated);
    // A violation that names an expectation is at the expectation, which is what the scenario wrote wrong.
    const at = ({ data }: (typeof world.violations)[number]) =>
      "expectation" in data
        ? expectationPlaces[data.expectation]
        : "scenarioLine" in data && data.scenarioLine !== null
          ? linePlaces[data.scenarioLine]
          : undefined;
    for (const violation of [...world.violations, ...(world.halted === undefined ? [] : [world.halted])])
      violations.push(toReported(violation, at(violation) ?? named.place, { scenario: ref }));
    const halted = world.halted !== undefined || [...world.services.values()].some((p) => p.halted !== undefined);
    for (const v of stepOrderChanges(spec, scenario, simulated, 0))
      violations.push(toReported(v, v.location ?? named.place, { scenario: ref }));
    for (const service of world.services.keys()) {
      for (const v of serviceViolations(simulated, service))
        violations.push(
          toReported(v, v.location ?? (v.definition === null ? named.place : placeOf(spec, v.definition)), {
            scenario: ref,
          }),
        );
      const lines = snapshots.get(service) ?? [];
      const run = { service: named.service, scenario: named.name, runner: service };
      if (service === named.service || lines.length > 0) snapshotted.push({ run, lines: halted ? undefined : lines });
    }
  }
  return { violations, snapshotted };
}

/** The parts that `test --coverage` reports, each at its definition, in place order. */
export const uncoveredOf = (spec: Spec, reached: Coverage): ReportedViolation[] =>
  uncoveredParts(spec.structure, reached)
    .map((violation) => ({ violation, place: placeOf(spec, violation.definition) }))
    .sort((x, y) => comparePlaces(x.place, y.place))
    .map(reportedOfFound);
