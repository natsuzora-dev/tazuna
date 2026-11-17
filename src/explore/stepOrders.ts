import type { ChoiceDependent, StepName } from "../data/choiceDependent.generated.ts";
import type { Origin, Scenario } from "../data/scenario.generated.ts";
import { canonicalJson, type Json } from "../data/values.ts";
import { type Violation, type ViolationValue, withExtra } from "../data/violation.ts";
import { placeOf } from "../load/found.ts";
import type { Spec } from "../load/load.ts";
import { stepNameDefinition } from "../service/note.ts";
import { created } from "../service/state.ts";
import type { Span, StepOrder } from "../sim/network.ts";
import { executeSpec, type Made, snapshotsOf } from "../sim/spec/simulate.ts";
import { leadsTo } from "../sim/trace.ts";
import { compareTrace } from "../verify/compare.ts";
import { type Compare, type Outcome, outcomeOf, stepOrder, stepOrderLimit } from "./choiceDependent.ts";

/** Lean's Tried: a step order that the search ran, refused (Execution.refused) or with the violation found, if any. */
export type Tried =
  | { readonly order: readonly StepName[]; readonly refused: true }
  | { readonly order: readonly StepName[]; readonly found: ChoiceDependent | null };

/** Lean's Searched: what the search of the processing `origin` of `service` ran and found. The diff test asks Lean. */
export interface Searched {
  readonly origin: Origin;
  readonly service: string;
  readonly tried: readonly Tried[];
  readonly found: readonly ChoiceDependent[];
}

export type OnSearched = ((searched: Searched) => void) | undefined;

const violationValue = ({ kind, definition, data }: ViolationValue): ViolationValue => ({ kind, definition, data });

export const compareOf =
  (spec: Spec, service: string): Compare =>
  (expected, actual) => {
    const { found, set } = compareTrace(spec, service, expected, actual);
    const [mismatch] = found;
    return mismatch === undefined ? { set } : { mismatch: violationValue(mismatch) };
  };

/** Lean's Execution.outcome. */
export function outcomeFor(m: Made, service: string): Outcome {
  const p = m.world.participants.get(service);
  if (p === undefined) throw new Error(`${service} does not run`);
  const lines = snapshotsOf(m).get(service) ?? [];
  const keys = [...m.world.participants].flatMap(([q, r]) =>
    created(r.processing.state).map(([entity, key]) => [key, `${q}/${entity}`] as const),
  );
  return outcomeOf(
    p.halted === undefined ? null : violationValue(p.halted),
    lines,
    p.processing.state.records,
    new Map(keys),
  );
}

/** Lean's Execution.refused. */
function refused(m: Made, service: string): boolean {
  const kind = m.world.participants.get(service)?.halted?.kind;
  return kind === "InvalidInput.unreadyStep" || kind === "InvalidInput.unusedStepOrder";
}

/** Lean's Execution.span?. */
const spanOf = (m: Made, origin: Origin, service: string): Span | undefined =>
  m.world.spans.find((s) => s.service === service && canonicalJson(s.origin as Json) === canonicalJson(origin as Json));

/** Lean's Execution.taken. */
function taken(m: Made, span: Span): (readonly [number, StepName])[] {
  const steps = m.world.participants.get(span.service)?.processing.state.steps ?? [];
  const collected = m.listeners.get(span.service)?.collected;
  return (collected?.names(span.stepsFrom) ?? []).filter(
    ([n, name]) =>
      n < span.stepsTo && (name.kind !== "deadline" || steps[n]?.tie !== undefined) && steps[n]?.barrier !== true,
  );
}

/** Lean's Execution.haltedIn. */
function haltedIn(m: Made, span: Span): boolean {
  if (m.world.participants.get(span.service)?.halted === undefined) return false;
  const last = m.world.spans.findLast((s) => s.service === span.service);
  return last !== undefined && canonicalJson(last.origin as Json) === canonicalJson(span.origin as Json);
}

/** Lean's Execution.candidatesOf. */
function candidatesOf(m: Made, span: Span): (readonly [number, number])[] {
  const p = m.world.participants.get(span.service);
  if (p === undefined || haltedIn(m, span)) return [];
  const collected = m.listeners.get(span.service)?.collected;
  return (collected?.candidates(p.processing.st, p.processing.state, span.stepsFrom) ?? []).filter(
    ([i]) => i < span.stepsTo,
  );
}

/** Lean's findingKey. */
const findingKey = (v: ChoiceDependent): string =>
  v.kind === "ChoiceDependent.stepOrder"
    ? canonicalJson([v.data.firstStep, v.data.secondStep, v.data.difference] as unknown as Json)
    : "";

/** Lean's stepOrderSearch of the processing `origin` of `service` of the scenario `prefix`, which ends with it. */
function stepOrderSearch(
  spec: Spec,
  prefix: Scenario,
  origin: Origin,
  service: string,
): Pick<Searched, "tried" | "found"> {
  const base = executeSpec(spec, prefix);
  const baseSpan = spanOf(base, origin, service);
  if (baseSpan === undefined || candidatesOf(base, baseSpan).length === 0) return { tried: [], found: [] };
  const compare = compareOf(spec, service);
  const tried: Tried[] = [];
  const found: ChoiceDependent[] = [];
  const reached = new Set([canonicalJson(taken(base, baseSpan).map(([, name]) => name) as Json)]);
  const queue: { readonly executed: Made; readonly order: readonly StepName[] }[] = [{ executed: base, order: [] }];
  let first: StepName | undefined;
  for (let next = queue.shift(); next !== undefined; next = queue.shift()) {
    const { executed, order: parentOrder } = next;
    const span = spanOf(executed, origin, service);
    if (span === undefined) continue;
    const names = taken(executed, span);
    const nameOf = new Map(names);
    const steps = executed.world.participants.get(service)?.processing.state.steps ?? [];
    const parentOutcome = outcomeFor(executed, service);
    for (const [i, j] of candidatesOf(executed, span)) {
      const [a, b] = [nameOf.get(i), nameOf.get(j)];
      if (a === undefined || b === undefined) continue;
      const order = [
        ...names.filter(([n]) => n < i).map(([, name]) => name),
        ...names.filter(([n]) => i < n && n < j && leadsTo(steps, n, j)).map(([, name]) => name),
        b,
        a,
      ];
      const key = canonicalJson(order as Json);
      if (tried.some((t) => canonicalJson(t.order as Json) === key)) continue;
      first ??= a;
      if (tried.length === stepOrderLimit) {
        const limit: ChoiceDependent = {
          kind: "ChoiceDependent.searchLimit",
          definition: stepNameDefinition(first),
          data: { limit: stepOrderLimit },
        };
        return { tried, found: [...found, limit] };
      }
      const stepOrders: StepOrder[] = [{ origin, service, order }];
      const alternative = executeSpec(spec, prefix, stepOrders);
      if (refused(alternative, service)) {
        tried.push({ order, refused: true });
        continue;
      }
      const result = stepOrder(compare, a, b, parentOrder, order, parentOutcome, outcomeFor(alternative, service));
      tried.push({ order, found: result ?? null });
      if (result !== undefined && !found.some((v) => findingKey(v) === findingKey(result))) found.push(result);
      const altSpan = spanOf(alternative, origin, service);
      if (altSpan === undefined) continue;
      const sequence = canonicalJson(taken(alternative, altSpan).map(([, name]) => name) as Json);
      if (reached.has(sequence)) continue;
      reached.add(sequence);
      queue.push({ executed: alternative, order });
    }
  }
  return { tried, found };
}

/**
 * Lean's stepOrderChanges, as violations at the definitions they name: the step orders that change the result of each
 * processing of the execution `executed` of the scenario `sc` whose origin is the startup (when `from` is 0) or a line from
 * `from` on. `onSearched` receives each search.
 */
export function stepOrderChanges(
  spec: Spec,
  sc: Scenario,
  executed: Made,
  from: number,
  onSearched?: OnSearched,
): Violation[] {
  const searched = new Set<string>();
  return executed.world.spans.flatMap((span) => {
    const index = span.origin.type === "startup" ? -1 : span.origin.index;
    const key = canonicalJson([span.origin, span.service] as Json);
    if ((span.origin.type === "startup" ? from > 0 : index < from) || searched.has(key)) return [];
    searched.add(key);
    if (candidatesOf(executed, span).length === 0) return [];
    const prefix: Scenario = { ...sc, lines: sc.lines.slice(0, index + 1), expectations: [] };
    const search = stepOrderSearch(spec, prefix, span.origin, span.service);
    if (search.tried.length === 0 && search.found.length === 0) return [];
    onSearched?.({ origin: span.origin, service: span.service, ...search });
    return search.found.map((v) => withExtra(v, { location: placeOf(spec, v.definition) }));
  });
}
