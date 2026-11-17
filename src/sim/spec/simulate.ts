import type { Report } from "../../data/report.generated.ts";
import type { GivenRecord, Scenario } from "../../data/scenario.generated.ts";
import type { TraceLine } from "../../data/trace.generated.ts";
import type { Violation } from "../../data/violation.ts";
import type { Spec } from "../../load/load.ts";
import { Collect } from "../../observe/instrument.ts";
import { snapshotLines } from "../../observe/trace.ts";
import type { Processing } from "../../service/chart/queue.ts";
import { created } from "../../service/state.ts";
import type { Structure } from "../../syntax/structure.generated.ts";
import { encodedGivenRecords, start } from "../given.ts";
import type { Assignment, StepOrder, World } from "../network.ts";
import { simulate, walk } from "../run.ts";
import { instrumented, Listener } from "./listener.ts";
import { newProcessing } from "./processing.ts";

/**
 * Returns the processing of the running service `service` of the spec, whose records Given places, with the functions
 * instrumented as Lean's Instrument does, collecting into the listener.
 */
function processingFor(spec: Spec, service: string, listener: Listener): Processing {
  const functions = instrumented(spec, service, listener);
  return newProcessing(functions.st, functions, listener, undefined);
}

export const givenRecordsOf = (spec: Spec, sc: Scenario, service: string): GivenRecord[] =>
  encodedGivenRecords(processingFor(spec, service, new Listener(spec, new Collect())), sc, service);

export interface Made {
  readonly world: World;
  readonly listeners: ReadonlyMap<string, Listener>;
}

function made(
  spec: Spec,
  sc: Scenario,
  run: (structure: Structure, w: World, sc: Scenario) => World,
  stepOrders: readonly StepOrder[],
  assignments: readonly Assignment[] = [],
): Made {
  const listeners = new Map<string, Listener>();
  const w = start(sc, (service) => {
    const listener = new Listener(spec, new Collect());
    listeners.set(service, listener);
    return processingFor(spec, service, listener);
  });
  w.stepOrders = stepOrders;
  w.assignments = assignments;
  return { world: run(spec.structure, w, sc), listeners };
}

/** Runs the scenario on the spec's services, each processing taking the steps of its entry of `stepOrders` first. */
export const simulateSpec = (spec: Spec, sc: Scenario, stepOrders: readonly StepOrder[] = []): Made =>
  made(spec, sc, simulate, stepOrders);

/** Runs the lines of the scenario on the spec's services as explore does (walk), with the handles of `assignments`. */
export const walkSpec = (
  spec: Spec,
  sc: Scenario,
  stepOrders: readonly StepOrder[] = [],
  assignments: readonly Assignment[] = [],
): Made => made(spec, sc, walk, stepOrders, assignments);

/** Each running service's trace as its snapshot holds it. */
export const snapshotsOf = ({ world, listeners }: Made): ReadonlyMap<string, readonly TraceLine[]> =>
  new Map(
    [...world.participants].map(([service, p]) => {
      const s = p.processing.state;
      const causes = (listeners.get(service) as Listener).collected.causes;
      return [
        service,
        snapshotLines(
          s.lines,
          causes,
          created(s).map(([, key]) => key),
        ),
      ];
    }),
  );

/**
 * Lean's reportedViolations of a running service: its own violations, then those its listener collected, then its
 * halt.
 */
export function participantViolations({ world, listeners }: Made, service: string): Violation[] {
  const p = world.participants.get(service);
  if (p === undefined) return [];
  return [
    ...p.processing.state.violations,
    ...(listeners.get(service)?.collected.violations ?? []),
    ...(p.halted === undefined ? [] : [p.halted]),
  ];
}

/** Lean's candidates of a running service: none once it halted. */
function participantCandidates({ world, listeners }: Made, service: string): (readonly [number, number])[] {
  const p = world.participants.get(service);
  if (p === undefined || p.halted !== undefined) return [];
  return listeners.get(service)?.collected.candidates(p.processing.st, p.processing.state, 0) ?? [];
}

/**
 * What a simulation shows: each running service's trace, violations and candidates, and the reports and halting
 * report.
 */
export interface Outcome {
  readonly participants: readonly {
    readonly service: string;
    readonly lines: readonly TraceLine[];
    readonly violations: readonly Pick<Violation, "kind" | "definition" | "data">[];
    readonly candidates: readonly (readonly [number, number])[];
  }[];
  readonly reports: readonly Report[];
  readonly halted: Report | null;
}

const violationValue = ({ kind, definition, data }: Violation) => ({ kind, definition, data });

export const outcomeOf = (m: Made): Outcome => ({
  participants: [...m.world.participants].map(([service, p]) => ({
    service,
    lines: p.processing.state.lines,
    violations: participantViolations(m, service).map(violationValue),
    candidates: participantCandidates(m, service),
  })),
  reports: m.world.reports,
  halted: m.world.halted ?? null,
});
