import type { ChoiceDependent, StepName } from "../data/choiceDependent.generated.ts";
import { invalidInputKinds } from "../data/invalidInput.generated.ts";
import type { Origin, Scenario } from "../data/scenario.generated.ts";
import { canonicalJson, type Json } from "../data/values.ts";
import { type Violation, type ViolationValue, withExtra } from "../data/violation.ts";
import { placeOf } from "../load/found.ts";
import type { Spec } from "../load/load.ts";
import { type Compare, type Outcome, outcomeOf, stepOrder, stepOrderLimit } from "../observe/choiceDependent.ts";
import { leadsTo } from "../observe/trace.ts";
import { stepNameDefinition } from "../service/note.ts";
import type { Span, StepOrder } from "../sim/network.ts";
import { type Made, participantViolations, snapshotsOf, walkSpec } from "../sim/spec/simulate.ts";
import { compareTrace } from "../verify/compare.ts";

/**
 * A step order that the search decided: the scenario walked up to the processing, the processing (`origin` of
 * `service`), the order, and the violation found against the walk without the order, if any. The diff test asks Lean
 * the same.
 */
export interface DecidedOrder {
  readonly scenario: Scenario;
  readonly origin: Origin;
  readonly service: string;
  readonly order: readonly StepName[];
  readonly found: ChoiceDependent | undefined;
}

export type DecidedOrders = ((decided: DecidedOrder) => void) | undefined;

const violationValue = ({ kind, definition, data }: ViolationValue): ViolationValue => ({ kind, definition, data });

const compareOf =
  (spec: Spec, service: string): Compare =>
  (expected, actual) => {
    const { found, bindings } = compareTrace(spec, service, expected, actual);
    const [mismatch] = found;
    return mismatch === undefined ? { bindings } : { mismatch: violationValue(mismatch) };
  };

/** What the relation compares of the walk `m` for `service`: its halt, or its trace and records. */
function outcomeFor(m: Made, service: string): Outcome {
  const p = m.world.participants.get(service);
  if (p === undefined) throw new Error(`${service} does not run`);
  const lines = snapshotsOf(m).get(service) ?? [];
  return outcomeOf(p.halted === undefined ? null : violationValue(p.halted), lines, p.processing.state.records);
}

const invalidInput: ReadonlySet<string> = new Set(invalidInputKinds);

/** The reports and InvalidInput violations of a walk, which an order that no one could take adds. */
const refusals = (m: Made): number =>
  m.world.reports.length +
  (m.world.halted === undefined ? 0 : 1) +
  [...m.world.participants.keys()].reduce(
    (n, service) => n + participantViolations(m, service).filter((v) => invalidInput.has(v.kind)).length,
    0,
  );

/** The span of the walk's processing `origin` of `service`. */
const spanOf = (m: Made, origin: Origin, service: string): Span | undefined =>
  m.world.spans.find((s) => s.service === service && canonicalJson(s.origin as Json) === canonicalJson(origin as Json));

/**
 * The steps that a processing's internal queue took, by step number and name, in the order they began: those that
 * began while no step was open, except the steps of deadlines and barriers, which no order takes.
 */
function taken(m: Made, span: Span): (readonly [number, StepName])[] {
  const steps = m.world.participants.get(span.service)?.processing.state.steps ?? [];
  const collected = m.listeners.get(span.service)?.collected;
  return (collected?.names(span.stepsFrom) ?? []).filter(
    ([n, name]) => n < span.stepsTo && name.kind !== "deadline" && steps[n]?.barrier !== true,
  );
}

/** Lean's candidates of the processing of `span`. */
function candidatesOf(m: Made, span: Span): (readonly [number, number])[] {
  const p = m.world.participants.get(span.service);
  if (p === undefined || p.halted !== undefined) return [];
  const collected = m.listeners.get(span.service)?.collected;
  return (collected?.candidates(p.processing.state.steps, span.stepsFrom) ?? []).filter(([i]) => i < span.stepsTo);
}

/**
 * Returns the step orders of the processing `origin` of `service`, the last of the walk `prefix`, that change its
 * result. Starting from the walk without an order, each pair of a walk's candidates is run in the other order: the steps
 * before the pair as that walk took them, then the steps between the pair that lead to the second, the second, and the
 * first. Each walk that reaches a new order of taken steps is searched in turn, so the search reaches every order of
 * dependent steps (dynamic partial-order reduction, Flanagan and Godefroid, POPL 2005), up to stepOrderLimit orders.
 * Each order is compared with the walk without one.
 */
function searchProcessing(
  spec: Spec,
  prefix: Scenario,
  origin: Origin,
  service: string,
  decided: DecidedOrders,
): ChoiceDependent[] {
  const base = walkSpec(spec, prefix);
  const span = spanOf(base, origin, service);
  if (span === undefined || candidatesOf(base, span).length === 0) return [];
  const compare = compareOf(spec, service);
  const original = outcomeFor(base, service);
  const found = new Map<string, ChoiceDependent>();
  const tried = new Set<string>();
  const reached = new Set([canonicalJson(taken(base, span).map(([, name]) => name) as Json)]);
  const queue: Made[] = [base];
  let first: StepName | undefined;
  for (let walked = queue.shift(); walked !== undefined; walked = queue.shift()) {
    const at = spanOf(walked, origin, service) as Span;
    const names = taken(walked, at);
    const nameOf = new Map(names);
    const steps = walked.world.participants.get(service)?.processing.state.steps ?? [];
    for (const [i, j] of candidatesOf(walked, at)) {
      const [a, b] = [nameOf.get(i), nameOf.get(j)];
      if (a === undefined || b === undefined) continue;
      const order = [
        ...names.filter(([n]) => n < i).map(([, name]) => name),
        ...names.filter(([n]) => i < n && n < j && leadsTo(steps, n, j)).map(([, name]) => name),
        b,
        a,
      ];
      const key = canonicalJson(order as Json);
      if (tried.has(key)) continue;
      first ??= a;
      if (tried.size === stepOrderLimit) {
        const limit: ChoiceDependent = {
          kind: "ChoiceDependent.searchLimit",
          definition: stepNameDefinition(first),
          data: { limit: stepOrderLimit },
        };
        return [...found.values(), limit];
      }
      tried.add(key);
      const stepOrders: StepOrder[] = [{ origin, service, order }];
      const alternative = walkSpec(spec, prefix, stepOrders);
      if (refusals(alternative) > refusals(base)) continue;
      const result = stepOrder(compare, a, b, original, outcomeFor(alternative, service));
      decided?.({ scenario: prefix, origin, service, order, found: result });
      if (result !== undefined) found.set(canonicalJson(result as unknown as Json), result);
      const altSpan = spanOf(alternative, origin, service);
      if (altSpan === undefined) continue;
      const sequence = canonicalJson(taken(alternative, altSpan).map(([, name]) => name) as Json);
      if (reached.has(sequence)) continue;
      reached.add(sequence);
      queue.push(alternative);
    }
  }
  return [...found.values()];
}

/**
 * Returns the step orders that change the result of each processing of the walk `walked` of the scenario `sc` whose
 * origin is the begin (when `from` is 0) or a line from `from` on, each at the definition it names.
 */
export function stepOrderChanges(
  spec: Spec,
  sc: Scenario,
  walked: Made,
  from: number,
  decided?: DecidedOrders,
): Violation[] {
  const searched = new Set<string>();
  return walked.world.spans.flatMap((span) => {
    const index = span.origin.type === "begin" ? -1 : span.origin.index;
    const key = canonicalJson([span.origin, span.service] as Json);
    if ((span.origin.type === "begin" ? from > 0 : index < from) || searched.has(key)) return [];
    searched.add(key);
    if (candidatesOf(walked, span).length === 0) return [];
    const prefix: Scenario = { ...sc, lines: sc.lines.slice(0, index + 1), expectations: [] };
    return searchProcessing(spec, prefix, span.origin, span.service, decided).map((v) =>
      withExtra(v, { location: placeOf(spec, v.definition) }),
    );
  });
}
