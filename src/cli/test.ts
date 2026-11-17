import { mkdirSync, rmSync, writeFileSync } from "node:fs";
import { dirname } from "node:path";
import { type DefinitionRef, sameRef } from "../data/definitionRef.ts";
import type { TraceLine } from "../data/trace.generated.ts";
import { toJsonl } from "../data/trace.ts";
import { peerSnapshotName, snapshotEntryPath, snapshotPath } from "../data/traceFile.ts";
import type { Uncovered } from "../data/uncovered.ts";
import { canonicalJson } from "../data/values.ts";
import { type ReportedViolation, toReported } from "../data/violation.ts";
import type { Named } from "../dsl/definition.ts";
import { assignmentChanges } from "../explore/assignments.ts";
import { exploreLines, seenLines, valuesPerPayload } from "../explore/paths.ts";
import { stepOrderChanges } from "../explore/stepOrders.ts";
import * as automations from "../explore/uncovered/automations.ts";
import * as charts from "../explore/uncovered/charts.ts";
import * as requests from "../explore/uncovered/requests.ts";
import { comparePlaces, type Found, placeOf, reportedOfFound } from "../load/found.ts";
import type { Spec } from "../load/load.ts";
import type { LoadedScenario } from "../load/scenarios.ts";
import { Coverage } from "../sim/spec/coverage.ts";
import { serviceViolations, simulateSpec, snapshotsOf } from "../sim/spec/simulate.ts";
import { pairingViolation } from "../verify/pairing.ts";
import { pairSnapshots, snapshotFolders, snapshotViolations } from "../verify/snapshot.ts";

const uncoveredChecks: readonly {
  readonly check: (spec: Spec, reached: Coverage) => readonly Found<Uncovered>[];
}[] = [requests, automations, charts];

export interface TestResult {
  readonly violations: readonly ReportedViolation[];
  readonly written: readonly string[];
  readonly removed: readonly string[];
  readonly reached: Coverage;
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
): Pick<TestResult, "violations" | "written" | "removed"> {
  const refOf = (s: Snapshotted) => ({ service: s.scenario.service, name: s.name });
  const ended = snapshotted.filter((s) => s.lines !== undefined);
  const linesOf = (s: Snapshotted) => s.lines as readonly TraceLine[];
  const written = update ? ended.map((s) => writeSnapshot(spec, refOf(s), linesOf(s))) : [];
  const { services, folders } = snapshotFolders(spec);
  const scenarios = snapshotted.map((s) => ({ ...refOf(s), compared: s.lines !== undefined }));
  const pairing = pairSnapshots(services, scenarios, folders);
  const violations = update
    ? []
    : ended
        .filter((s) => pairing.compare.some((r) => sameRef(r, refOf(s))))
        .flatMap((s) => snapshotViolations(spec, refOf(s), linesOf(s)));
  const removed: string[] = [];
  for (const p of pairing.violations)
    if (update && p.violation.kind === "Uncomparable.obsoleteSnapshot" && "snapshotEntry" in p.at) {
      const path = snapshotEntryPath(spec, p.at);
      rmSync(path);
      removed.push(path);
    } else if ("scenario" in p.at) {
      const { scenario } = snapshotted.find((s) =>
        sameRef(refOf(s), (p.at as { scenario: DefinitionRef }).scenario),
      ) as Snapshotted;
      violations.push(toReported(p.violation, scenario.place));
    } else violations.push(pairingViolation(spec, p));
  return { violations, written, removed };
}

/**
 * Simulates and explores every scenario, then tests the snapshots (testSnapshots). A scenario still written as an input
 * list, which only verify's examples keep until verify runs the simulation, is not run: its snapshot is kept as it is.
 */
export function testSpec(spec: Spec, options: { readonly update: boolean; readonly depth: number }): TestResult {
  const bounds = { depth: options.depth, valuesPerPayload };
  const reached = new Coverage();
  const simulated = simulateScenarios(spec);
  const violations: ReportedViolation[] = [];
  const reported = new Set<string>();
  // Two violations count as one when they differ only in `error`.
  const report = (violation: ReportedViolation) => {
    const key = canonicalJson([violation.kind, violation.definition, violation.data, violation.location]);
    if (reported.has(key)) return;
    reported.add(key);
    violations.push(violation);
  };
  for (const p of simulated.violations) report(p);
  const seenInLines = seenLines(spec);
  for (const named of spec.scenarios) {
    const explored = exploreLines(spec, named as Named<LoadedScenario>, seenInLines, bounds);
    reached.addAll(explored.reached);
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
  const snapshots = testSnapshots(spec, simulated.snapshotted, options.update);
  return { ...snapshots, violations: [...violations, ...snapshots.violations], reached };
}

/**
 * Simulates each scenario and returns the violations that it reports, each at the line it names, with the step orders
 * that change the result of one of its processings and the assignment of its handles of `requests` that changes the
 * result of a running service, and the trace of each
 * running service when the simulation did not halt: the own service's under the scenario's name, and each running
 * peer's that has lines under peerSnapshotName.
 */
function simulateScenarios(spec: Spec): {
  readonly violations: ReportedViolation[];
  readonly snapshotted: Snapshotted[];
} {
  const violations: ReportedViolation[] = [];
  const snapshotted: Snapshotted[] = [];
  for (const named of spec.scenarios) {
    const { scenario, linePlaces } = named.definition as LoadedScenario;
    const ref = { service: named.service, name: named.name };
    const simulated = simulateSpec(spec, scenario);
    const { world } = simulated;
    const snapshots = snapshotsOf(simulated);
    const at = (line: number | null | undefined) =>
      line === null || line === undefined ? undefined : linePlaces[line];
    for (const report of [...world.violations, ...(world.halted === undefined ? [] : [world.halted])]) {
      const line = "scenarioLine" in report.data ? report.data.scenarioLine : undefined;
      violations.push(toReported(report, at(line) ?? named.place, { scenario: ref }));
    }
    const halted = world.halted !== undefined || [...world.services.values()].some((p) => p.halted !== undefined);
    for (const v of [...stepOrderChanges(spec, scenario, simulated, 0), ...assignmentChanges(spec, scenario)])
      violations.push(toReported(v, v.location ?? named.place, { scenario: ref }));
    for (const service of world.services.keys()) {
      for (const v of serviceViolations(simulated, service))
        violations.push(
          toReported(v, v.location ?? (v.definition === null ? named.place : placeOf(spec, v.definition)), {
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
  return { violations, snapshotted };
}

export const uncoveredOf = (spec: Spec, reached: Coverage): ReportedViolation[] =>
  uncoveredChecks
    .flatMap((c) => c.check(spec, reached))
    .sort((x, y) => comparePlaces(x.place, y.place))
    .map(reportedOfFound);
