import { InternalError } from "../src/data/internalError.ts";
import type { Line, Scenario } from "../src/data/scenario.generated.ts";
import { type Obligation, uncovered } from "../src/data/uncovered.ts";
import { canonicalJson, type Json, plain } from "../src/data/values.ts";
import type { Violation } from "../src/data/violation.ts";
import { stateValue } from "../src/explore/choiceDependent.ts";
import { enabled } from "../src/explore/enabled.ts";
import { worldFingerprint } from "../src/explore/fingerprint.ts";
import { type Executed, enabledLines, executeAppended, executeMove, type Move } from "../src/explore/paths.ts";
import { uncoveredParts } from "../src/explore/uncovered.ts";
import type { Spec } from "../src/load/load.ts";
import { Halt } from "../src/service/state.ts";
import type { RunningService } from "../src/sim/network.ts";
import { NoCache } from "../src/sim/spec/cache.ts";
import { Coverage } from "../src/sim/spec/coverage.ts";
import { SpecFunctions } from "../src/sim/spec/functions.ts";
import { outcomeOf } from "../src/sim/spec/simulate.ts";
import { SimFunctions } from "./lean/functions.ts";
import type { Lean } from "./lean/lean.ts";

const violationValue = ({ kind, definition, data }: Violation) => ({ kind, definition, data });

const byCanonical = (a: unknown, b: unknown) => (canonicalJson(a) < canonicalJson(b) ? -1 : 1);

/**
 * What an execution of `sc` shows, as Lean's reply to `simulate` with `execute` and `explore` gives it: with the parts
 * that each service reached, and for the own service the moves that explore appends next and what `test --coverage`
 * reports of this execution alone.
 */
export function executedOutcome(spec: Spec, sc: Scenario, executed: Executed) {
  const { world, listeners } = executed;
  const moves = enabledLines(spec, sc);
  const all = new Coverage();
  for (const l of listeners.values()) all.addAll(l.coverage);
  return {
    ...outcomeOf(executed),
    services: outcomeOf(executed).services.map((p) => {
      const { processing, halted } = world.services.get(p.service) as RunningService;
      const reached = (listeners.get(p.service)?.coverage.keys() ?? [])
        .map((k) => uncovered(JSON.parse(k) as Obligation))
        .sort(byCanonical);
      const own = p.service === sc.service ? { uncovered: uncoveredParts(spec.structure, all) } : {};
      if (halted !== undefined) return { ...p, reached, ...own };
      const functions = new SpecFunctions(spec, p.service);
      const state = plain(stateValue(processing.st, processing.state, (schema, v) => functions.encode(schema, v)));
      try {
        const next = enabled(processing);
        return p.service === sc.service
          ? { ...p, enabled: next, moves: moves(sc.lines, executed), state, reached, ...own }
          : { ...p, enabled: next, state, reached };
      } catch (error) {
        if (!(error instanceof Halt)) throw error;
        return { ...p, fault: violationValue(error.violation), state, reached, ...own };
      }
    }),
  };
}

/** `value` as data, each Map and Set as its entries in order. */
function data(value: unknown, path: readonly object[] = []): Json {
  if (value === undefined) return null;
  if (value === null || typeof value !== "object") return value as Json;
  if (path.includes(value)) throw new InternalError("an execution holds a cycle");
  const inner = (v: unknown) => data(v, [...path, value]);
  if (value instanceof Map) return ["Map", ...[...value].map(([k, v]) => [inner(k), inner(v)])];
  if (value instanceof Set) return ["Set", ...[...value].map(inner)];
  if (Array.isArray(value)) return value.map(inner);
  return Object.fromEntries(Object.entries(value).map(([k, v]) => [k, inner(v)]));
}

/**
 * The whole of an execution as data: every field of its world, each processing's state and queue, and every field of
 * each listener. The functions, the service and the spec are left out, since a continued execution shares them with the
 * one it continues.
 */
function executionData({ world, listeners }: Executed): Json {
  const services = new Map(
    [...world.services].map(([service, { processing, halted }]) => [
      service,
      { state: processing.state, queue: processing.queue, halted },
    ]),
  );
  const heard = new Map(
    [...listeners].map(([service, l]) => [
      service,
      Object.fromEntries(Object.entries(l).filter(([k]) => k !== "spec")),
    ]),
  );
  return data({ ...world, services, listeners: heard });
}

/**
 * The run that an execution with the evaluation cache differs from: Lean's, the TS run without the cache, or the TS run
 * continued from its parent's execution (`incremental`); or, for `fingerprint`, two worlds that one of TS and Lean
 * takes as the same and the other does not, with the other's two fingerprints.
 */
export interface Difference {
  readonly against: "lean" | "noCache" | "incremental" | "fingerprint";
  readonly ts: string;
  readonly other: string;
}

/** The explored worlds by TS's and Lean's fingerprints, which must take the same worlds as the same. */
export class SameWorlds {
  private readonly leanOf = new Map<string, string>();
  private readonly tsOf = new Map<string, string>();

  /** Adds a world, and returns the difference when one fingerprint matches an earlier world's and the other does not. */
  add(ts: string, lean: string): Difference | undefined {
    const known = { lean: this.leanOf.get(ts), ts: this.tsOf.get(lean) };
    if (known.lean !== undefined && known.lean !== lean) return { against: "fingerprint", ts: known.lean, other: lean };
    if (known.ts !== undefined && known.ts !== ts) return { against: "fingerprint", ts: known.ts, other: ts };
    this.leanOf.set(ts, lean);
    this.tsOf.set(lean, ts);
    return undefined;
  }
}

/** An execution of the scenario with `appended` after its lines, which a longer one can continue from. */
export interface Parent {
  readonly executed: Executed;
  readonly appended: readonly Line[];
}

/**
 * Executes the scenario with `appended` after its lines in TS with the evaluation cache, in TS without it, in TS
 * continued from `parent` when given, and in Lean, and adds the world to `worlds`. Returns the continued execution, or
 * else the cached one, and the first run whose outcome differs from the cached one.
 */
export function executeEach(
  lean: Lean,
  spec: Spec,
  sc: Scenario,
  appended: readonly Line[],
  worlds: SameWorlds,
  parent?: Parent,
): { readonly executed: Executed; readonly difference?: Difference } {
  const replayed = executeAppended(spec, sc, appended);
  const executed =
    parent === undefined
      ? replayed
      : executeMove(spec, sc, parent.appended, parent.executed, appended.slice(parent.appended.length));
  const plainRun = executeAppended(spec, sc, appended, () => new NoCache());
  const extended = { ...sc, lines: [...sc.lines, ...appended] };
  const ts = canonicalJson(executedOutcome(spec, extended, replayed) as unknown as Json);
  const uncached = canonicalJson(executedOutcome(spec, extended, plainRun) as unknown as Json);
  if (ts !== uncached) return { executed, difference: { against: "noCache", ts, other: uncached } };
  if (parent !== undefined) {
    const [whole, continued] = [canonicalJson(executionData(replayed)), canonicalJson(executionData(executed))];
    if (continued !== whole) return { executed, difference: { against: "incremental", ts: whole, other: continued } };
  }
  const functions = new SimFunctions(spec, (part) => lean.read(part));
  const { outcome, fingerprint } = lean.explored(spec, extended, functions);
  const fromLean = canonicalJson(outcome);
  if (fromLean !== ts) return { executed, difference: { against: "lean", ts, other: fromLean } };
  const merged = worlds.add(worldFingerprint(replayed.world), fingerprint);
  return merged === undefined ? { executed } : { executed, difference: merged };
}

/**
 * Returns lines that no one could write after an execution: a clock line before now, a request and an operation whose
 * value its schema rejects, an answer to the first awaited request with a rejection reason its target never gives, and
 * a subscription's end of a line that opened none.
 */
export function invalidLines(spec: Spec, sc: Scenario, executed: Executed, enabledLines: readonly Line[]): Move[] {
  const malformed = { value: "not an object", holes: [] };
  const command = spec.structure.definitions.find((d) => d.kind === "command" && d.service === sc.service);
  const answer = enabledLines.find((l) => l.type === "answer");
  const operate = enabledLines.find((l) => l.type === "operate");
  const lines: Line[] = [
    { type: "at", time: executed.world.now - 1 },
    { type: "unsubscribe", subscription: 0 },
    ...(command === undefined
      ? []
      : [
          {
            type: "request",
            kind: "command",
            target: { service: command.service, name: command.name },
            input: malformed,
          } as const,
        ]),
    ...(answer?.type === "answer"
      ? [
          {
            ...answer,
            answer: { value: { result: "rejected", rejection: { kind: "requires", reason: "unlisted" } }, holes: [] },
          },
        ]
      : []),
    ...(operate?.type === "operate" ? [{ ...operate, payload: malformed }] : []),
  ];
  return lines.map((line) => [line]);
}
