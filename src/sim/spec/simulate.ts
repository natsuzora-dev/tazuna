import type { InvalidScenario } from "../../data/invalidScenario.generated.ts";
import type { GivenRecord, Scenario } from "../../data/scenario.generated.ts";
import type { TraceLine } from "../../data/trace.generated.ts";
import type { Violation } from "../../data/violation.ts";
import { Collect } from "../../explore/instrument.ts";
import type { Spec } from "../../load/load.ts";
import type { Processing } from "../../service/chart/queue.ts";
import { created } from "../../service/state.ts";
import type { Structure } from "../../spec/structure.generated.ts";
import { encodedGivenRecords, start } from "../given.ts";
import type { StepOrder, World } from "../network.ts";
import { execute, simulate } from "../run.ts";
import { snapshotLines, traceLineOf } from "../trace.ts";
import { instrumented, Listener } from "./listener.ts";
import { newProcessing } from "./processing.ts";

/**
 * Returns the processing of the running service `service` of the spec, whose records Given places, with the functions
 * instrumented as Lean's Instrument does, collecting into the listener.
 */
function processingFor(spec: Spec, service: string, listener: Listener): Processing {
  const functions = instrumented(spec, service, listener);
  return newProcessing(functions.st, functions, listener, spec.services.get(service)?.place);
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
): Made {
  const listeners = new Map<string, Listener>();
  const w = start(sc, (service) => {
    const listener = new Listener(spec, new Collect());
    listeners.set(service, listener);
    return processingFor(spec, service, listener);
  });
  w.stepOrders = stepOrders;
  return { world: run(spec.structure, w, sc), listeners };
}

/** Runs the scenario on the spec's services, each processing taking the steps of its entry of `stepOrders` first. */
export const simulateSpec = (spec: Spec, sc: Scenario, stepOrders: readonly StepOrder[] = []): Made =>
  made(spec, sc, simulate, stepOrders);

/** Runs the lines of the scenario on the spec's services as explore does (execute). */
export const executeSpec = (spec: Spec, sc: Scenario, stepOrders: readonly StepOrder[] = []): Made =>
  made(spec, sc, execute, stepOrders);

/** Each running service's trace as its snapshot holds it. */
export const snapshotsOf = ({ world }: Made): ReadonlyMap<string, readonly TraceLine[]> =>
  new Map(
    [...world.services].map(([service, p]) => {
      const s = p.processing.state;
      return [
        service,
        snapshotLines(
          service,
          s.lines,
          s.steps,
          created(s).map(([, key]) => key),
        ),
      ];
    }),
  );

/**
 * Lean's reportedViolations of a running service: its own violations, then those its listener collected, then its
 * halt.
 */
export function serviceViolations({ world, listeners }: Made, service: string): Violation[] {
  const p = world.services.get(service);
  if (p === undefined) return [];
  return [
    ...p.processing.state.violations,
    ...(listeners.get(service)?.collected.violations ?? []),
    ...(p.halted === undefined ? [] : [p.halted]),
  ];
}

/** Lean's candidates of a running service: none once it halted. */
function serviceCandidates({ world, listeners }: Made, service: string): (readonly [number, number])[] {
  const p = world.services.get(service);
  if (p === undefined || p.halted !== undefined) return [];
  return listeners.get(service)?.collected.candidates(p.processing.state, 0) ?? [];
}

/**
 * What a simulation shows: each running service's trace, violations and candidates, and the InvalidScenario
 * violations and the halting one.
 */
export interface Outcome {
  readonly services: readonly {
    readonly service: string;
    readonly lines: readonly TraceLine[];
    readonly violations: readonly Pick<Violation, "kind" | "definition" | "data">[];
    readonly candidates: readonly (readonly [number, number])[];
  }[];
  readonly violations: readonly InvalidScenario[];
  readonly halted: InvalidScenario | null;
}

const violationValue = ({ kind, definition, data }: Violation) => ({ kind, definition, data });

export const outcomeOf = (m: Made): Outcome => ({
  services: [...m.world.services].map(([service, p]) => ({
    service,
    lines: p.processing.state.lines.map((l) => traceLineOf(service, l)),
    violations: serviceViolations(m, service).map(violationValue),
    candidates: serviceCandidates(m, service),
  })),
  violations: m.world.violations,
  halted: m.world.halted ?? null,
});
