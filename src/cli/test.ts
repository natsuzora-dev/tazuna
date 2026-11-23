import { mkdirSync, rmSync, writeFileSync } from "node:fs";
import { dirname } from "node:path";
import type { CheckedSpec } from "../check/spec.ts";
import { InternalError } from "../data/internalError.ts";
import type { TraceLine } from "../data/trace.generated.ts";
import { toJsonl } from "../data/trace.ts";
import { type Run, sameRun, snapshotEntryPath, snapshotPath } from "../data/traceFile.ts";
import { canonicalJson } from "../data/values.ts";
import { type Location, type ReportedViolation, toReported, type ViolationValue } from "../data/violation.ts";
import type { Named } from "../dsl/definition.ts";
import { placeOf } from "../load/found.ts";
import type { Spec } from "../load/load.ts";
import type { LoadedScenario } from "../load/scenarios.ts";
import { snapshotPairingViolation } from "../verify/pairing.ts";
import { pairSnapshots, snapshotFolders, snapshotViolations } from "../verify/snapshot.ts";
import { ask } from "./engine.ts";

export interface TestResult {
  readonly violations: readonly ReportedViolation[];
  readonly written: readonly string[];
  readonly removed: readonly string[];
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
 * Where a violation that a running service reports is: a failed service invariant, or a throw or a notOnly of one, at
 * the service, since a service is no definition; any other at its definition, or at the scenario without one.
 */
function placeOfReported(spec: Spec, named: Named<LoadedScenario>, v: ViolationValue, service?: string): Location {
  const atService =
    v.kind === "Fault.failedServiceInvariant" ||
    ((v.kind === "Fault.exception" || v.kind === "Fault.notOnly") && v.definition === null);
  const servicePlace = service === undefined ? undefined : spec.services.get(service)?.place;
  if (atService && servicePlace !== undefined) return servicePlace;
  return v.definition === null ? named.place : placeOf(spec, v.definition);
}

/**
 * Simulates `scenarios`, some or all of the spec's, in the engine, then tests the snapshots (testSnapshots). Each
 * violation is reported once per kind, definition, data and location, in the order of the scenarios.
 */
export function testSpec(
  spec: CheckedSpec,
  options: { readonly update: boolean; readonly scenarios: readonly Named<LoadedScenario>[] },
): TestResult {
  const { scenarios } = options;
  const [tested] = ask("test", [{ structure: spec.structure, scenarios: scenarios.map((s) => s.definition.scenario) }]);
  if (tested === undefined) throw new InternalError("the engine gave no answer to test");
  const violations: ReportedViolation[] = [];
  const reported = new Set<string>();
  // Two violations count as one when they differ only in `error`.
  const report = (violation: ReportedViolation) => {
    const key = canonicalJson([violation.kind, violation.definition, violation.data, violation.location]);
    if (reported.has(key)) return;
    reported.add(key);
    violations.push(violation);
  };
  const snapshotted: Snapshotted[] = [];
  const runs = scenarios.map((named, i) => {
    const run = tested.runs[i];
    if (run === undefined) throw new InternalError(`the engine gave no run of ${named.service}/${named.name}`);
    return { named, run, ref: { service: named.service, name: named.name } };
  });
  for (const { named, run, ref } of runs) {
    const { linePlaces, expectationPlaces } = named.definition;
    // A violation that names an expectation is at the expectation, which is what the scenario wrote wrong.
    const at = ({ data }: ViolationValue) =>
      typeof data["expectation"] === "number"
        ? expectationPlaces[data["expectation"]]
        : typeof data["scenarioLine"] === "number"
          ? linePlaces[data["scenarioLine"]]
          : undefined;
    for (const v of run.violations) report(toReported(v, at(v) ?? named.place, { scenario: ref }));
    for (const { service, violations: own, lines } of run.services) {
      for (const v of own) report(toReported(v, placeOfReported(spec, named, v, service), { scenario: ref }));
      const snapshotRun = { service: named.service, scenario: named.name, runner: service };
      if (service === named.service || lines.length > 0)
        snapshotted.push({ run: snapshotRun, lines: run.halted ? undefined : lines });
    }
  }
  const skipped = spec.scenarios.filter((s) => !scenarios.includes(s));
  const snapshots = testSnapshots(spec, snapshotted, options.update, skipped);
  return { ...snapshots, violations: [...violations, ...snapshots.violations] };
}
