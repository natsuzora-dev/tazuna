import { expectFound, InternalError } from "../../data/internalError.ts";
import type { InvalidScenario } from "../../data/invalidScenario.generated.ts";
import type { GivenRecord, Scenario } from "../../data/scenario.generated.ts";
import type { TraceLine } from "../../data/trace.generated.ts";
import type { Violation } from "../../data/violation.ts";
import { Collect } from "../../explore/instrument.ts";
import type { Spec } from "../../load/load.ts";
import type { Processing } from "../../service/chart/queue.ts";
import { cloneState, created } from "../../service/state.ts";
import type { Structure } from "../../spec/structure.generated.ts";
import { encodedGivenRecords, start } from "../given.ts";
import type { RunningService, StepOrder, World } from "../network.ts";
import { execute, executeFrom, simulate } from "../run.ts";
import { snapshotLines, traceLineOf } from "../trace.ts";
import { Cache } from "./cache.ts";
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
  cache: () => Cache = () => new Cache(),
): Made {
  const listeners = new Map<string, Listener>();
  const w = start(sc, (service) => {
    const listener = new Listener(spec, new Collect(), cache());
    listeners.set(service, listener);
    return processingFor(spec, service, listener);
  });
  w.stepOrders = stepOrders;
  return { world: run(spec.structure, w, sc), listeners };
}

/** Runs the scenario on the spec's services, each processing taking the steps of its entry of `stepOrders` first. */
export const simulateSpec = (spec: Spec, sc: Scenario, stepOrders: readonly StepOrder[] = []): Made =>
  made(spec, sc, simulate, stepOrders);

/**
 * Runs the lines of the scenario on the spec's services as explore does (execute), each service's listener with an
 * evaluation cache from `cache`.
 */
export const executeSpec = (
  spec: Spec,
  sc: Scenario,
  stepOrders: readonly StepOrder[] = [],
  cache?: () => Cache,
): Made => made(spec, sc, execute, stepOrders, cache);

/**
 * A copy of `m` between lines that a run can continue apart from `m`. Each processing gets a copy of its listener as
 * its note and evaluations, and functions instrumented over that copy. Messages are copied, since a run sets their
 * status; the logs that a run only appends to are copied and their entries shared. Every world field is listed, as in
 * cloneState.
 */
function cloneMade(spec: Spec, m: Made): Made {
  const listeners = new Map<string, Listener>();
  const services = new Map(
    [...m.world.services].map(([service, { processing: p, halted }]): [string, RunningService] => {
      const listener = expectFound(`listener of ${service}`, m.listeners.get(service)).clone();
      listeners.set(service, listener);
      const q = p.queue;
      const queue = { tasks: [...q.tasks], round: [...q.round], commands: [...q.commands], entered: [...q.entered] };
      const functions = instrumented(spec, service, listener);
      const processing = { ...p, state: cloneState(p.state), queue, functions, note: listener, evaluations: listener };
      return [service, { processing, halted }];
    }),
  );
  const w = m.world;
  const world: World = {
    now: w.now,
    roles: w.roles,
    services,
    messages: w.messages.map((message) => ({ ...message })),
    spans: [...w.spans],
    opened: [...w.opened],
    sent: [...w.sent],
    carried: [...w.carried],
    leftInFlight: [...w.leftInFlight],
    counts: new Map([...w.counts].map(([k, byName]) => [k, new Map(byName)])),
    violations: [...w.violations],
    halted: w.halted,
    stepOrders: w.stepOrders,
  };
  return { world, listeners };
}

/**
 * Continues the execution `parent` of the lines of `sc` before `from` with the lines from `from` on, leaving `parent`
 * as it is. The plain method is executeSpec of all the lines, which the diff tests compare it with. `parent` has no
 * InvalidScenario violation: when Given reports one, execute takes no line, and a world does not tell Given's
 * violations from a line's.
 */
export function executeSpecFrom(spec: Spec, sc: Scenario, parent: Made, from: number): Made {
  if (parent.world.violations.length > 0) throw new InternalError("continuing a world with InvalidScenario violations");
  const child = cloneMade(spec, parent);
  executeFrom(child.world, sc, from);
  return child;
}

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
