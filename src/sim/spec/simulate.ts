import type { Report } from "../../data/report.generated.ts";
import type { GivenRecord, Scenario } from "../../data/scenario.generated.ts";
import type { TraceLine } from "../../data/trace.generated.ts";
import type { Violation } from "../../data/violation.ts";
import type { Spec } from "../../load/load.ts";
import { Collect } from "../../observe/instrument.ts";
import type { Processing } from "../../service/chart/queue.ts";
import type { World } from "../network.ts";
import { simulate, start } from "../run.ts";
import { Listener } from "./execute.ts";
import { SpecFunctions } from "./functions.ts";
import { newProcessing } from "./processing.ts";

/** Returns the Given records of the running service `service`. */
function givenRecords(sc: Scenario, service: string): readonly GivenRecord[] {
  if (service === sc.service) return sc.given.records;
  const peer = sc.given.peers.find((p) => p.service === service);
  return peer?.role === "run" ? peer.records : [];
}

/** Returns the processing of the running service `service` of the spec, with its Given records. */
function processingFor(spec: Spec, sc: Scenario, service: string): Processing {
  const listener = new Listener(spec, service, new Collect());
  const functions = new SpecFunctions(spec, service, listener);
  const r = newProcessing(functions.st, functions, listener, undefined);
  const { records } = r.state;
  for (const g of givenRecords(sc, service)) {
    const row = functions.givenRow(g.entity, g.value);
    if (g.key === undefined) records.singles.set(g.entity, row);
    else records.keyed.get(g.entity)?.set(g.key, row);
  }
  return r;
}

/** Runs the scenario on the spec's services. */
export const simulateSpec = (spec: Spec, sc: Scenario): World =>
  simulate(
    start(sc, (service) => processingFor(spec, sc, service)),
    sc,
  );

/** What a simulation shows: each running service's trace and violations, and the reports and halting report. */
export interface Outcome {
  readonly participants: readonly {
    readonly service: string;
    readonly lines: readonly TraceLine[];
    readonly violations: readonly Pick<Violation, "kind" | "definition" | "data">[];
  }[];
  readonly reports: readonly Report[];
  readonly halted: Report | null;
}

const violationValue = ({ kind, definition, data }: Violation) => ({ kind, definition, data });

export const outcomeOf = (w: World): Outcome => ({
  participants: [...w.participants].map(([service, p]) => ({
    service,
    lines: p.processing.state.lines,
    violations: [...p.processing.state.violations, ...(p.halted === undefined ? [] : [p.halted])].map(violationValue),
  })),
  reports: w.reports,
  halted: w.halted ?? null,
});
