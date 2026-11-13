import type { ChoiceDependent, StepName } from "../data/choiceDependent.generated.ts";
import type { DeadlineId } from "../data/trace.generated.ts";
import { canonicalJson } from "../data/values.ts";
import { type Location, type Violation, type ViolationValue, withExtra } from "../data/violation.ts";
import type { AnyCommand, AnyQuery, Place } from "../dsl/definition.ts";
import type { Input } from "../dsl/scenario.ts";
import { placeOf } from "../load/found.ts";
import type { Spec } from "../load/load.ts";
import { refOfDefinition } from "../load/traceName.ts";
import {
  answerChoice,
  answerOrder,
  type Compare,
  deadlineOrder,
  type Outcome,
  outcomeOf,
  requestOrder,
  stepOrder,
} from "../observe/choiceDependent.ts";
import { leadsTo } from "../observe/trace.ts";
import type { Run } from "../run/execute.ts";
import { compareTrace } from "../verify/prepare.ts";
import { type Child, givable, type Ordered } from "./moves.ts";

export type Target = AnyCommand | AnyQuery;

/**
 * A map from each request to a spec service to the requests to that service that a sender sent while it waited for its
 * answer, with the place of that sender.
 */
export type Concurrent = ReadonlyMap<Target, ReadonlyMap<Target, Place>>;

/**
 * A pair of runs that the relation decided: the kind of choice, the two runs in the order the relation takes them, and
 * the finding, if any. The runs differ first at the choice, so their steps name it.
 */
export interface Candidate {
  readonly kind: "deadlineOrder" | "answerChoice" | "answerOrder" | "requestOrder" | "stepOrder";
  readonly runs: readonly [Run, Run];
  readonly found: ChoiceDependent | undefined;
}

/** A listener for each pair of runs that the relation decides; the diff test compares them with Lean. */
export type Decided = ((candidate: Candidate) => void) | undefined;

/**
 * An order or a choice whose result differs from the other's: `inputs` follow the parent and reach the result that
 * differs.
 */
export interface Changed {
  readonly violation: Violation;
  readonly inputs: readonly Input[];
}

const violationValue = ({ kind, definition, data }: ViolationValue): ViolationValue => ({ kind, definition, data });

/** Returns what the relation compares of `run`; `at` lists the run's swapped input lines, which its lines gather. */
const outcomeOfRun = (run: Run, at?: readonly number[]): Outcome =>
  outcomeOf(run.halted === undefined ? null : violationValue(run.halted), run.outcome.lines, run.records, at);

/** Returns verify's first violation, or else its bindings, as the relation reads them. */
const compareOf =
  (spec: Spec, service: string): Compare =>
  (expected, actual) => {
    const { found, bindings } = compareTrace(spec, service, expected, actual);
    const [mismatch] = found;
    return mismatch === undefined ? { bindings } : { mismatch: violationValue(mismatch) };
  };

const changed = (found: ChoiceDependent, place: Location, inputs: readonly Input[]): Changed => ({
  violation: withExtra(found, { location: place }),
  inputs,
});

const toOf = (input: Input): string | undefined => (input.type === "answer" ? input.choice?.to : undefined);

const orderOf = (input: Input): readonly DeadlineId[] => input.deadlineOrder ?? [];

const withoutOrder = ({ deadlineOrder: _, ...input }: Input): Input => input as Input;

const sameOrder = (a: Input, b: Input): boolean => canonicalJson(orderOf(a)) === canonicalJson(orderOf(b));

const targetOf = (input: Input): Target | undefined =>
  input.type === "command" ? input.command : input.type === "query" ? input.query : undefined;

const inputOf = (input: Input): unknown =>
  input.type === "command" || input.type === "query" ? input.input : undefined;

/**
 * Returns the first input that chooses otherwise than `own` at one of its forks and changes the result: another order
 * of the deadlines in its ties, or another request that the trace cannot tell from the one its `to` names. An answer
 * choice is at `place`.
 */
function changedFork(
  spec: Spec,
  compare: Compare,
  parent: Run,
  own: Child,
  ordered: Ordered,
  place: Location,
  decided: Decided,
): Changed | undefined {
  // The outcome is built lazily, at the first fork to compare, because most inputs have no fork.
  let ownOutcome: Outcome | undefined;
  const ownOf = () => {
    ownOutcome ??= outcomeOfRun(own.result);
    return ownOutcome;
  };
  const siblings = (input: Input) => ordered(input).filter((c) => givable(parent, c.result));
  for (const sibling of siblings(withoutOrder(own.input)).filter((c) => !sameOrder(c.input, own.input))) {
    const [mine, theirs] = [orderOf(own.input), orderOf(sibling.input)];
    const k = theirs.findIndex((d, i) => canonicalJson(d) !== canonicalJson(mine[i]));
    const [a, b] = [mine[k] as DeadlineId, theirs[k] as DeadlineId];
    const found = deadlineOrder(
      compare,
      (d) => own.result.chartOf(d.instance),
      a,
      b,
      ownOf(),
      outcomeOfRun(sibling.result),
    );
    decided?.({ kind: "deadlineOrder", runs: [own.result, sibling.result], found });
    if (found === undefined) continue;
    // The alternative is the run whose deadline comes second in the pair.
    const alternative = canonicalJson(found.data.firstDeadline) === canonicalJson(a) ? sibling.input : own.input;
    return changed(found, found.definition === null ? place : placeOf(spec, found.definition), [alternative]);
  }
  const request = toOf(own.input);
  if (own.input.type !== "answer" || request === undefined) return undefined;
  const { target, answer, time } = own.input;
  for (const other of parent.alikeRequests(request))
    for (const sibling of siblings({
      type: "answer",
      sender: other.sender as never,
      target,
      answer,
      choice: { to: other.id },
      time,
    })) {
      const sender = refOfDefinition(spec, own.input.sender);
      const found = answerChoice(compare, sender, request, other.id, ownOf(), outcomeOfRun(sibling.result));
      decided?.({ kind: "answerChoice", runs: [own.result, sibling.result], found });
      if (found !== undefined) return changed(found, place, [sibling.input]);
    }
  return undefined;
}

/**
 * Returns the orders of two steps that `own` took after `parent` that change the result. For each pair whose other
 * order explore runs (Lean's candidates), `own` runs again from `parent` with a `stepOrder` that takes the steps before
 * the pair as `own` took them, then the steps between the pair that lead to the second, the second, and the first.
 * This follows dynamic partial-order reduction (Flanagan and Godefroid, POPL 2005), which runs the other order of each
 * dependent pair and reports only a property that the other order violates. It approximates every order: each pair is
 * swapped once from the order `own` took, so a result that only an order of three or more steps changes, which no
 * single swap gives, is not reported. `step` continues a run by an input.
 */
export function stepOrderChanges(
  spec: Spec,
  service: string,
  parent: Run,
  own: Child,
  options: { readonly step: (run: Run, input: Input) => Run; readonly decided: Decided },
): Changed[] {
  const { names, candidates } = own.result.stepsFrom(parent.steps.length);
  if (candidates.length === 0) return [];
  const compare = compareOf(spec, service);
  const steps = own.result.steps;
  // The internal queue takes each step that began while no step was open, except the steps of deadlines and barriers.
  const taken = names.filter(([n, name]) => name.kind !== "deadline" && steps[n]?.barrier !== true);
  // Each step of a candidate is one of `names`.
  const nameOf = new Map(names);
  const found: Changed[] = [];
  for (const [i, j] of candidates) {
    const [a, b] = [nameOf.get(i) as StepName, nameOf.get(j) as StepName];
    const input: Input = {
      ...own.input,
      stepOrder: [
        ...taken.filter(([n]) => n < i).map(([, name]) => name),
        ...taken.filter(([n]) => i < n && n < j && leadsTo(steps, n, j)).map(([, name]) => name),
        b,
        a,
      ],
    };
    const alternative = options.step(parent, input);
    if (!givable(parent, alternative)) continue;
    const result = stepOrder(compare, a, b, outcomeOfRun(own.result), outcomeOfRun(alternative));
    options.decided?.({ kind: "stepOrder", runs: [own.result, alternative], found: result });
    if (result === undefined) continue;
    // The alternative is the run whose step comes second in the pair, at the definition of the pair's first step.
    const first = canonicalJson(result.data.firstStep) === canonicalJson(a);
    found.push(changed(result, placeOf(spec, result.definition), [first ? input : own.input]));
  }
  return found;
}

/**
 * Two inputs whose order nobody controls after a parent, `first` and `second` in the order the runs are made, and the
 * finding when the result of `first` then `second` (`forward`) differs from the other order: its place, and whether
 * the backward run is its alternative.
 */
interface Unordered {
  readonly first: Input;
  readonly second: Input;
  readonly kind: "answerOrder" | "requestOrder";
  readonly decide: (
    forward: Outcome,
    backward: Outcome,
  ) => { readonly found: ChoiceDependent; readonly place: Place | undefined; readonly backward: boolean } | undefined;
}

/**
 * Returns the pair of `a` and `b` when nobody controls their order after `parent`: two answers that screens await at
 * once, which arrive on separate connections, or two requests to a spec service of which one was sent while the other
 * waited for its answer. Two requests with the same target and the same input are not compared, because running them in
 * the other order is the same run with the ids swapped.
 */
function unordered(
  spec: Spec,
  parent: Run,
  a: Input,
  b: Input,
  concurrent: Concurrent,
  compare: Compare,
): Unordered | undefined {
  if (a.type === "answer" && b.type === "answer") {
    const [x, y] = [toOf(a), toOf(b)];
    const screens = a.sender.kind === "screen" && b.sender.kind === "screen";
    if (!screens || x === undefined || y === undefined || x === y || !parent.waits(x) || !parent.waits(y))
      return undefined;
    return {
      first: a,
      second: b,
      kind: "answerOrder",
      decide: (forward, backward) => {
        const senders = [refOfDefinition(spec, a.sender), refOfDefinition(spec, b.sender)] as const;
        const found = answerOrder(compare, x, y, ...senders, forward, backward);
        if (found === undefined) return undefined;
        return { found, place: placeOf(spec, found.definition), backward: found.data.firstRequestId === x };
      },
    };
  }
  const [t, u] = [targetOf(a), targetOf(b)];
  if (t === undefined || u === undefined) return undefined;
  if (t === u && canonicalJson(inputOf(a)) === canonicalJson(inputOf(b))) return undefined;
  const forward = concurrent.get(t)?.get(u);
  const place = forward ?? concurrent.get(u)?.get(t);
  if (place === undefined) return undefined;
  const [first, second, f, s] = forward === undefined ? [b, a, u, t] : [a, b, t, u];
  const [firstRef, secondRef] = [refOfDefinition(spec, f), refOfDefinition(spec, s)];
  return {
    first,
    second,
    kind: "requestOrder",
    decide: (forward, backward) => {
      const found = requestOrder(compare, firstRef, secondRef, forward, backward);
      return found === undefined ? undefined : { found, place, backward: true };
    },
  };
}

/** Returns a command or query with the id that its line has in `run`, the result of input `n`. */
function withId(input: Input, run: Run, n: number): Input {
  if (input.type !== "command" && input.type !== "query") return input;
  const id = run.outcome.lines[run.inputLines[n] as number]?.id;
  return id === undefined ? input : { ...input, id };
}

/**
 * Returns the orders and choices after `parent` that change the result: `own` against the inputs that choose otherwise
 * at its forks, and against each of `others` whose order with it nobody controls, run in both orders. `step` continues
 * a run by an input; `after` gives the result of an input of `others` after the parent; `place` is the place of a
 * change that no sender causes.
 */
export function orderChanges(
  spec: Spec,
  service: string,
  parent: Run,
  own: Child,
  others: readonly Input[],
  options: {
    readonly ordered: Ordered;
    readonly concurrent: Concurrent;
    readonly step: (run: Run, input: Input) => Run;
    readonly after: (input: Input) => Run;
    readonly place: Location;
    readonly decided: Decided;
  },
): Changed[] {
  const compare = compareOf(spec, service);
  const fork = changedFork(spec, compare, parent, own, options.ordered, options.place, options.decided);
  const found: Changed[] = fork === undefined ? [] : [fork];
  const after = (input: Input) => (input === own.input ? own.result : options.after(input));
  for (const other of others) {
    const pair = unordered(spec, parent, own.input, other, options.concurrent, compare);
    if (pair === undefined) continue;
    const { first, second } = pair;
    const n = parent.inputLines.length;
    // A request without an id gets the next id of the trace, so the backward order gives each request its forward id.
    const forward = options.step(after(first), second);
    const [a, b] = [withId(first, after(first), n), withId(second, forward, n + 1)];
    const unchanged = b === second;
    const backward = options.step(unchanged ? after(second) : options.step(parent, b), a);
    if (!givable(parent, forward) || !givable(parent, backward)) continue;
    const decided = pair.decide(
      outcomeOfRun(forward, [forward.inputLines[n] as number, forward.inputLines[n + 1] as number]),
      outcomeOfRun(backward, [backward.inputLines[n + 1] as number, backward.inputLines[n] as number]),
    );
    options.decided?.({ kind: pair.kind, runs: [forward, backward], found: decided?.found });
    if (decided !== undefined)
      found.push(changed(decided.found, decided.place ?? options.place, decided.backward ? [b, a] : [a, b]));
  }
  return found;
}
