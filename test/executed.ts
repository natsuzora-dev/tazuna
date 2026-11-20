import type { Line, Scenario } from "../src/data/scenario.generated.ts";
import { type Obligation, uncovered } from "../src/data/uncovered.ts";
import { canonicalJson, type Json, plain } from "../src/data/values.ts";
import type { Violation } from "../src/data/violation.ts";
import { stateValue } from "../src/explore/choiceDependent.ts";
import { enabled } from "../src/explore/enabled.ts";
import { worldFingerprint } from "../src/explore/fingerprint.ts";
import {
  type Executed,
  enabledLines,
  executeAppended,
  type Move,
  seenLines,
  valuesPerPayload,
} from "../src/explore/paths.ts";
import { uncoveredParts } from "../src/explore/uncovered.ts";
import type { Spec } from "../src/load/load.ts";
import type { LoadedScenario } from "../src/load/scenarios.ts";
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
  const moves = enabledLines(spec, sc, seenLines(spec), valuesPerPayload);
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

/**
 * The run that an execution with the evaluation cache differs from: Lean's, or the TS run without the cache; or, for
 * `fingerprint`, two worlds that one of TS and Lean takes as the same and the other does not, with the other's two
 * fingerprints.
 */
export interface Difference {
  readonly against: "lean" | "noCache" | "fingerprint";
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

/**
 * Executes the scenario with `appended` after its lines in TS with the evaluation cache, in TS without it, and in Lean,
 * and adds the world to `worlds`. Returns the cached TS execution, and the first run whose outcome differs from it.
 */
export function executeEach(
  lean: Lean,
  spec: Spec,
  sc: Scenario,
  appended: readonly Line[],
  worlds: SameWorlds,
): { readonly executed: Executed; readonly difference?: Difference } {
  const executed = executeAppended(spec, sc, appended);
  const plainRun = executeAppended(spec, sc, appended, () => new NoCache());
  const extended = { ...sc, lines: [...sc.lines, ...appended] };
  const ts = canonicalJson(executedOutcome(spec, extended, executed) as unknown as Json);
  const uncached = canonicalJson(executedOutcome(spec, extended, plainRun) as unknown as Json);
  if (ts !== uncached) return { executed, difference: { against: "noCache", ts, other: uncached } };
  const functions = new SimFunctions(spec, (part) => lean.read(part));
  const explore = {
    scenarios: spec.scenarios.map((s) => (s.definition as LoadedScenario).scenario),
    valuesPerPayload,
  };
  const { outcome, fingerprint } = lean.explored(spec, extended, functions, explore);
  const fromLean = canonicalJson(outcome);
  if (fromLean !== ts) return { executed, difference: { against: "lean", ts, other: fromLean } };
  const merged = worlds.add(worldFingerprint(executed.world), fingerprint);
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
    { type: "at", time: executed.world.now.subtract({ milliseconds: 1 }).toString() },
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
