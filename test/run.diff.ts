import assert from "node:assert/strict";
import { join, relative } from "node:path";
import { after, test } from "node:test";
import { haltingFaultKinds } from "../src/data/fault.generated.ts";
import type { Line, Scenario } from "../src/data/scenario.generated.ts";
import type { RejectionKind } from "../src/data/trace.generated.ts";
import { canonicalJson, type Json } from "../src/data/values.ts";
import type { Violation } from "../src/data/violation.ts";
import { enabled } from "../src/explore/enabled.ts";
import {
  type Executed,
  enabledLines,
  executeAppended,
  type Move,
  seenLines,
  valuesPerPayload,
} from "../src/explore/paths.ts";
import { search } from "../src/explore/search.ts";
import type { Spec } from "../src/load/load.ts";
import type { LoadedScenario } from "../src/load/scenarios.ts";
import { limits as tsLimits } from "../src/service/limits.ts";
import { byCallerKinds } from "../src/service/message.ts";
import { Halt } from "../src/service/state.ts";
import type { RunningService } from "../src/sim/network.ts";
import { outcomeOf } from "../src/sim/spec/simulate.ts";
import { checkedRoot, depth, runExamples } from "./examples.ts";
import { SimFunctions } from "./lean/functions.ts";
import { Lean } from "./lean/lean.ts";

const tazuna = join(import.meta.dirname, "..");

const lean = new Lean();
after(() => lean.close());

const roots = runExamples();

const specs = await Promise.all(
  roots.map(async (root) => ({ name: relative(tazuna, root), spec: await checkedRoot(root) })),
);

test("byCallerKinds matches RejectionKind.byCaller of Lean, the limit values match Limit.max, and haltingFaultKinds has the Fault kind named exceeded and each limit's name", () => {
  const names = lean.names();
  assert.deepEqual(
    Object.fromEntries(Object.keys(names.byCaller).map((kind) => [kind, byCallerKinds.has(kind as RejectionKind)])),
    names.byCaller,
  );
  assert.deepEqual({ ...tsLimits }, names.limits);
  const halting: ReadonlySet<string> = new Set(haltingFaultKinds);
  assert.deepEqual(
    Object.keys(names.limits).filter(
      (limit) => !halting.has(`Fault.exceeded${limit.charAt(0).toUpperCase()}${limit.slice(1)}`),
    ),
    [],
  );
});

/** What an execution shows, as Lean's reply to `simulate` with `execute` gives it. */
function executedOutcome(executed: Executed) {
  const { world } = executed;
  return {
    ...outcomeOf(executed),
    services: outcomeOf(executed).services.map((p) => {
      const { processing, halted } = world.services.get(p.service) as RunningService;
      if (halted !== undefined) return p;
      try {
        return { ...p, enabled: enabled(processing) };
      } catch (error) {
        if (!(error instanceof Halt)) throw error;
        return { ...p, enabled: { fault: violationValue(error.violation) } };
      }
    }),
  };
}

const violationValue = ({ kind, definition, data }: Violation) => ({ kind, definition, data });

/**
 * Returns lines that no one could write after an execution, each placed only at the end of a path: a clock line before now, a
 * request and an operation whose value its schema rejects, an answer to the first awaited request with a rejection
 * reason its target never gives, and a subscription's end of a line that opened none.
 */
function invalidLines(spec: Spec, sc: Scenario, executed: Executed, enabledLines: readonly Line[]): Move[] {
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

for (const { name, spec } of specs) {
  const seen = seenLines(spec);
  for (const named of spec.scenarios)
    test(`${name}: ${named.service}/${named.name} and every path of up to ${depth} moves after it execute alike in TS and Lean`, (t) => {
      const sc = (named.definition as LoadedScenario).scenario;
      const functions = () => new SimFunctions(spec, (part) => lean.read(part));
      const appendedOf = new Map<Executed, readonly Line[]>();
      const both = (appended: readonly Line[]): Executed => {
        const executed = executeAppended(spec, sc, appended);
        appendedOf.set(executed, appended);
        const fromLean = lean.simulate(spec, { ...sc, lines: [...sc.lines, ...appended] }, functions(), true);
        assert.equal(
          canonicalJson(fromLean as Json),
          canonicalJson(executedOutcome(executed) as unknown as Json),
          `the executions differ after appending ${JSON.stringify(appended)}`,
        );
        return executed;
      };
      const enabledAfter = enabledLines(spec, sc, seen, valuesPerPayload);
      const invalid = new WeakSet<Move>();
      const made = new Map<Executed, Map<Move, Executed>>();
      const next = (path: readonly Move[], executed: Executed): Move[] => {
        const last = path.at(-1);
        const stopped =
          executed.world.halted !== undefined || [...executed.world.services.values()].some((p) => p.halted);
        if (stopped || (last !== undefined && invalid.has(last))) return [];
        const appended = appendedOf.get(executed) ?? [];
        let moves: Move[];
        try {
          moves = enabledAfter([...sc.lines, ...appended], executed);
        } catch (error) {
          if (error instanceof Halt) return [];
          throw error;
        }
        const children = new Map(moves.map((move) => [move, both([...appended, ...move])]));
        made.set(executed, children);
        const others = invalidLines(spec, sc, executed, moves.flat());
        for (const move of others) invalid.add(move);
        return [...children.keys(), ...others];
      };
      let paths = 0;
      for (const _ of search<Move, Executed>({
        start: { path: [], result: both([]) },
        bound: depth,
        step: (parent, move) => {
          const children = made.get(parent);
          const executed = children?.get(move);
          if (children === undefined || executed === undefined)
            return both([...(appendedOf.get(parent) ?? []), ...move]);
          children.delete(move);
          if (children.size === 0) made.delete(parent);
          return executed;
        },
        next,
        merge: "none",
      }))
        paths += 1;
      t.diagnostic(`${paths} paths`);
    });
}
