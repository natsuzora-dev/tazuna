import type { Line, Scenario } from "../src/data/scenario.generated.ts";
import { canonicalJson, type Json, plain } from "../src/data/values.ts";
import type { Violation } from "../src/data/violation.ts";
import { stateValue } from "../src/explore/choiceDependent.ts";
import { enabled } from "../src/explore/enabled.ts";
import { type Executed, executeAppended, type Move } from "../src/explore/paths.ts";
import type { Spec } from "../src/load/load.ts";
import { Halt } from "../src/service/state.ts";
import type { RunningService } from "../src/sim/network.ts";
import { NoCache } from "../src/sim/spec/cache.ts";
import { SpecFunctions } from "../src/sim/spec/functions.ts";
import { outcomeOf } from "../src/sim/spec/simulate.ts";
import { SimFunctions } from "./lean/functions.ts";
import type { Lean } from "./lean/lean.ts";

const violationValue = ({ kind, definition, data }: Violation) => ({ kind, definition, data });

/** What an execution shows, as Lean's reply to `simulate` with `execute` gives it. */
export function executedOutcome(spec: Spec, executed: Executed) {
  const { world } = executed;
  return {
    ...outcomeOf(executed),
    services: outcomeOf(executed).services.map((p) => {
      const { processing, halted } = world.services.get(p.service) as RunningService;
      if (halted !== undefined) return p;
      const functions = new SpecFunctions(spec, p.service);
      const state = plain(stateValue(processing.st, processing.state, (schema, v) => functions.encode(schema, v)));
      try {
        return { ...p, enabled: enabled(processing), state };
      } catch (error) {
        if (!(error instanceof Halt)) throw error;
        return { ...p, fault: violationValue(error.violation), state };
      }
    }),
  };
}

/** What an execution shows with what explore reads of it: the obligations each service reached. */
const cachedOutcome = (spec: Spec, executed: Executed) => ({
  ...executedOutcome(spec, executed),
  reached: [...executed.listeners].map(([service, l]) => [service, l.coverage.keys()]),
});

/** The run that an execution with the evaluation cache differs from: Lean's, or the TS run without the cache. */
export interface Difference {
  readonly against: "lean" | "noCache";
  readonly ts: string;
  readonly other: string;
}

/**
 * Executes the scenario with `appended` after its lines in TS with the evaluation cache, in TS without it, and in Lean.
 * Returns the cached TS execution, and the first run whose outcome differs from it.
 */
export function executeEach(
  lean: Lean,
  spec: Spec,
  sc: Scenario,
  appended: readonly Line[],
): { readonly executed: Executed; readonly difference?: Difference } {
  const executed = executeAppended(spec, sc, appended);
  const plainRun = executeAppended(spec, sc, appended, () => new NoCache());
  const cached = canonicalJson(cachedOutcome(spec, executed) as unknown as Json);
  const uncached = canonicalJson(cachedOutcome(spec, plainRun) as unknown as Json);
  if (cached !== uncached) return { executed, difference: { against: "noCache", ts: cached, other: uncached } };
  const ts = canonicalJson(executedOutcome(spec, executed) as unknown as Json);
  const functions = new SimFunctions(spec, (part) => lean.read(part));
  const fromLean = canonicalJson(lean.simulate(spec, { ...sc, lines: [...sc.lines, ...appended] }, functions, true));
  return fromLean === ts ? { executed } : { executed, difference: { against: "lean", ts, other: fromLean } };
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
