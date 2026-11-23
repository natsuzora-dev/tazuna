import { relative } from "node:path";
import type { DefinitionRef } from "../data/definitionRef.ts";
import { InternalError } from "../data/internalError.ts";
import type { PairingViolation, ScenarioAt, SnapshotEntry } from "../data/pairing.ts";
import { type Run, snapshotEntryPath } from "../data/traceFile.ts";
import { type ReportedViolation, toReported } from "../data/violation.ts";
import type { Spec } from "../load/load.ts";

export const scenarioOf = (run: Run): DefinitionRef => ({ service: run.service, name: run.scenario });

const snapshotEntryAt = (spec: Spec, at: SnapshotEntry) =>
  ({ file: relative(spec.root, snapshotEntryPath(spec, at.service, at.entry)) }) as const;

/** Returns a violation of pairing runs with snapshots at its place: a scenario, or an entry of a snapshot folder. */
export function snapshotPairingViolation(
  spec: Spec,
  { at, violation }: PairingViolation<ScenarioAt | SnapshotEntry>,
): ReportedViolation {
  if (at.kind === "snapshotEntry") return toReported(violation, snapshotEntryAt(spec, at));
  const scenario = spec.scenarios.find((s) => s.service === at.scenario.service && s.name === at.scenario.name);
  if (scenario === undefined) throw new InternalError(`no scenario ${at.scenario.service}.${at.scenario.name}`);
  return toReported(violation, scenario.place);
}
