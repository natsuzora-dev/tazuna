import type { ChoiceDependent } from "../data/choiceDependent.generated.ts";
import { stepOrderLimit } from "../data/limits.generated.ts";
import type { Origin, Scenario } from "../data/scenario.generated.ts";
import type { StepName } from "../data/step.generated.ts";
import type { LineId } from "../data/trace.generated.ts";
import { canonicalJson, type Json } from "../data/values.ts";
import { type Violation, type ViolationValue, withExtra } from "../data/violation.ts";
import { placeOf } from "../load/found.ts";
import type { Spec } from "../load/load.ts";
import { type Line, sameLineId } from "../service/message.ts";
import { sameStep, stepNameDefinition, stepsKey } from "../service/note.ts";
import { created, tieOf } from "../service/state.ts";
import { type Span, type StepOrder, sameOrigin } from "../sim/network.ts";
import { executeSpec, type Made, snapshotsOf } from "../sim/spec/simulate.ts";
import { snapshotLines } from "../sim/trace.ts";
import { compareRuns } from "../verify/compare.ts";
import { type Compare, type Outcome, outcomeOf, stepOrder } from "./choiceDependent.ts";
import { leadsTo } from "./instrument.ts";

/** Lean's Tried: a step order that the search ran, refused (Execution.refused) or with the violation found, if any. */
export type Tried =
  | { readonly order: readonly StepName[]; readonly refused: true }
  | { readonly order: readonly StepName[]; readonly found: ChoiceDependent | null };

/** Lean's Searched: what the search of the processing of `service` ran and found. The diff test asks Lean. */
export interface Searched {
  readonly origin: Origin;
  readonly service: string;
  readonly tried: readonly Tried[];
  readonly found: readonly ChoiceDependent[];
}

export type OnSearched = ((searched: Searched) => void) | undefined;

const violationValue = ({ kind, definition, data }: ViolationValue): ViolationValue => ({ kind, definition, data });

const compareOf =
  (spec: Spec, service: string): Compare =>
  (renamed, expected, actual) => {
    const { found, set } = compareRuns(spec, service, expected, actual, renamed);
    const [mismatch] = found;
    return mismatch === undefined ? { set } : { mismatch: violationValue(mismatch) };
  };

/** Lean's Execution.outcomeWith: the outcome of `service` in `m`, with its lines `lines` when given. */
function outcomeFor(m: Made, service: string, lines?: readonly Line[]): Outcome {
  const p = m.world.services.get(service);
  if (p === undefined) throw new Error(`${service} does not run`);
  const s = p.processing.state;
  const traceLines =
    lines === undefined
      ? (snapshotsOf(m).get(service) ?? [])
      : snapshotLines(
          service,
          lines,
          s.steps,
          created(s).map(([, key]) => key),
        );
  const keys = [...m.world.services].flatMap(([q, r]) =>
    created(r.processing.state).map(([entity, key]) => [key, `${q}/${entity}`] as const),
  );
  return outcomeOf(
    p.processing.st,
    p.halted === undefined ? null : violationValue(p.halted),
    traceLines,
    s.records,
    s.deadlines,
    new Map(keys),
  );
}

/** Lean's Execution.refused. */
function refused(m: Made, service: string): boolean {
  const kind = m.world.services.get(service)?.halted?.kind;
  return kind === "InvalidInput.unreadyStep" || kind === "InvalidInput.unusedStepOrder";
}

/** Lean's Execution.span?. */
const spanOf = (m: Made, origin: Origin, service: string): Span | undefined =>
  m.world.spans.find((s) => s.service === service && sameOrigin(s.origin, origin));

const linesOf = (m: Made, service: string): readonly Line[] =>
  m.world.services.get(service)?.processing.state.lines ?? [];

/** Lean's inIds: the ids of the `in` lines of `span`. */
const inIds = (lines: readonly Line[], span: Span): LineId[] =>
  lines.slice(span.from, span.to).flatMap((l) => (l.dir === "in" ? [l.id] : []));

/** Lean's alignTo: the lines with those of `span` in the order of the messages `ids`, each window as one. */
function alignTo(ids: readonly LineId[], span: Span, lines: readonly Line[]): Line[] {
  const within = lines.slice(span.from, span.to);
  const firstIn = within.findIndex((l) => l.dir === "in");
  const pre = firstIn < 0 ? within : within.slice(0, firstIn);
  const windows: Line[][] = [];
  for (const l of within.slice(pre.length)) {
    if (l.dir === "in" || windows.length === 0) windows.push([l]);
    else windows.at(-1)?.push(l);
  }
  const key = (window: readonly Line[]) => {
    const head = window[0];
    const n = head === undefined ? -1 : ids.findIndex((id) => sameLineId(id, head.id));
    return n < 0 ? ids.length : n;
  };
  const sorted = windows.map((w, n) => [w, key(w), n] as const).toSorted((a, b) => a[1] - b[1] || a[2] - b[2]);
  return [...lines.slice(0, span.from), ...pre, ...sorted.flatMap(([w]) => w), ...lines.slice(span.to)];
}

/** Lean's Execution.taken. */
function taken(m: Made, span: Span): (readonly [number, StepName])[] {
  const steps = m.world.services.get(span.service)?.processing.state.steps ?? [];
  const collected = m.listeners.get(span.service)?.collected;
  return (collected?.names(span.stepsFrom) ?? []).filter(
    ([n, name]) =>
      n < span.stepsTo && (name.kind !== "deadline" || tieOf(steps[n]) !== undefined) && steps[n]?.barrier !== true,
  );
}

/** Lean's Execution.haltedIn. */
function haltedIn(m: Made, span: Span): boolean {
  if (m.world.services.get(span.service)?.halted === undefined) return false;
  const last = m.world.spans.findLast((s) => s.service === span.service);
  return last !== undefined && sameOrigin(last.origin, span.origin);
}

/** Lean's Execution.candidatesOf. */
function candidatesOf(m: Made, span: Span): (readonly [number, number])[] {
  const p = m.world.services.get(span.service);
  if (p === undefined || haltedIn(m, span)) return [];
  const collected = m.listeners.get(span.service)?.collected;
  return (collected?.candidates(p.processing.state, span.stepsFrom) ?? []).filter(([i]) => i < span.stepsTo);
}

/** Lean's findingKey. */
const findingKey = (v: ChoiceDependent): string =>
  v.kind === "ChoiceDependent.stepOrder"
    ? canonicalJson([v.data.firstStep, v.data.secondStep, v.data.difference] as unknown as Json)
    : "";

/** Lean's stepOrderSearch of the processing of `service` while `origin` is processed, of `prefix`, which ends with it. */
function stepOrderSearch(
  spec: Spec,
  prefix: Scenario,
  origin: Origin,
  service: string,
): Pick<Searched, "tried" | "found"> {
  const base = executeSpec(spec, prefix);
  const baseSpan = spanOf(base, origin, service);
  if (baseSpan === undefined) return { tried: [], found: [] };
  if (candidatesOf(base, baseSpan).length === 0) return { tried: [], found: [] };
  const found: ChoiceDependent[] = [];
  const compare = compareOf(spec, service);
  const tried: Tried[] = [];
  const reached = new Set([stepsKey(taken(base, baseSpan).map(([, name]) => name))]);
  const queue: { readonly executed: Made; readonly order: readonly StepName[] }[] = [{ executed: base, order: [] }];
  let first: StepName | undefined;
  for (let next = queue.shift(); next !== undefined; next = queue.shift()) {
    const { executed, order: parentOrder } = next;
    const span = spanOf(executed, origin, service);
    if (span === undefined) continue;
    const names = taken(executed, span);
    const nameOf = new Map(names);
    const steps = executed.world.services.get(service)?.processing.state.steps ?? [];
    const parentOutcome = outcomeFor(executed, service);
    for (const [i, j] of candidatesOf(executed, span)) {
      const [a, b] = [nameOf.get(i), nameOf.get(j)];
      if (a === undefined || b === undefined) continue;
      const [last2, last] = parentOrder.slice(-2);
      // Lean's searchPair states why skipping the undo of the parent's own swap misses no order.
      if (last2 !== undefined && last !== undefined && sameStep(last2, a) && sameStep(last, b)) continue;
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
          definition: stepNameDefinition(service, first),
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
      const altSpan = spanOf(alternative, origin, service);
      const aligned =
        altSpan === undefined
          ? outcomeFor(alternative, service)
          : outcomeFor(
              alternative,
              service,
              alignTo(inIds(linesOf(executed, service), span), altSpan, linesOf(alternative, service)),
            );
      const result = stepOrder(compare, service, a, b, parentOrder, order, parentOutcome, aligned);
      tried.push({ order, found: result ?? null });
      if (result !== undefined && !found.some((v) => findingKey(v) === findingKey(result))) found.push(result);
      if (altSpan === undefined) continue;
      const sequence = stepsKey(taken(alternative, altSpan).map(([, name]) => name));
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
