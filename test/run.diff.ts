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
  enabledLines,
  type Move,
  seenLines,
  valuesPerPayload,
  type Walked,
  walkAppended,
} from "../src/explore/paths.ts";
import { search } from "../src/explore/search.ts";
import type { Spec } from "../src/load/load.ts";
import type { LoadedScenario } from "../src/load/scenarios.ts";
import { limits as tsLimits } from "../src/service/limits.ts";
import { byCallerKinds } from "../src/service/message.ts";
import { Halt } from "../src/service/state.ts";
import type { Participant } from "../src/sim/network.ts";
import { outcomeOf } from "../src/sim/spec/simulate.ts";
import { depth, loadRoot, runExamples } from "./examples.ts";
import { SimFunctions } from "./lean/functions.ts";
import { Lean } from "./lean/lean.ts";

const tazuna = join(import.meta.dirname, "..");

const lean = new Lean();
after(() => lean.close());

const roots = runExamples();

const specs = await Promise.all(
  roots.map(async (root) => ({ name: relative(tazuna, root), spec: await loadRoot(root) })),
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

/** What a walk shows, as Lean's reply to `simulate` with `walk` gives it. */
function walkedOutcome(walked: Walked) {
  const { world } = walked;
  return {
    ...outcomeOf(walked),
    participants: outcomeOf(walked).participants.map((p) => {
      const { processing, halted } = world.participants.get(p.service) as Participant;
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
 * Returns lines that no one could write after a walk, each placed only at the end of a path: a clock line before now, a
 * request and an operation whose value its schema rejects, an answer to the first awaited request with a rejection
 * reason its target never gives, and a subscription's end of a line that opened none.
 */
function invalidLines(spec: Spec, sc: Scenario, walked: Walked, enabledLines: readonly Line[]): Move[] {
  const malformed = { value: "not an object", holes: [] };
  const command = spec.structure.definitions.find((d) => d.kind === "command" && d.service === sc.service);
  const answer = enabledLines.find((l) => l.type === "answer");
  const operate = enabledLines.find((l) => l.type === "operate");
  const lines: Line[] = [
    { type: "at", time: walked.world.now.subtract({ milliseconds: 1 }).toString() },
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
    test(`${name}: ${named.service}/${named.name} and every path that appends up to ${depth} lines to it walk alike in TS and Lean`, (t) => {
      const sc = (named.definition as LoadedScenario).scenario;
      const functions = () => new SimFunctions(spec, (part) => lean.read(part));
      const appendedOf = new Map<Walked, readonly Line[]>();
      const both = (appended: readonly Line[]): Walked => {
        const walked = walkAppended(spec, sc, appended);
        appendedOf.set(walked, appended);
        const fromLean = lean.simulate(spec, { ...sc, lines: [...sc.lines, ...appended] }, functions(), true);
        assert.equal(
          canonicalJson(fromLean as Json),
          canonicalJson(walkedOutcome(walked) as unknown as Json),
          `the walks differ after appending ${JSON.stringify(appended)}`,
        );
        return walked;
      };
      const enabledAfter = enabledLines(spec, sc, seen, valuesPerPayload);
      const invalid = new WeakSet<Move>();
      const made = new Map<Walked, Map<Move, Walked>>();
      const next = (path: readonly Move[], walked: Walked): Move[] => {
        const last = path.at(-1);
        const stopped =
          walked.world.halted !== undefined || [...walked.world.participants.values()].some((p) => p.halted);
        if (stopped || (last !== undefined && invalid.has(last))) return [];
        const appended = appendedOf.get(walked) ?? [];
        let moves: Move[];
        try {
          moves = enabledAfter([...sc.lines, ...appended], walked);
        } catch (error) {
          if (error instanceof Halt) return [];
          throw error;
        }
        const children = new Map(moves.map((move) => [move, both([...appended, ...move])]));
        made.set(walked, children);
        const others = invalidLines(spec, sc, walked, moves.flat());
        for (const move of others) invalid.add(move);
        return [...children.keys(), ...others];
      };
      let paths = 0;
      for (const _ of search<Move, Walked>({
        start: { path: [], result: both([]) },
        bound: depth,
        step: (parent, move) => {
          const children = made.get(parent);
          const walked = children?.get(move);
          if (children === undefined || walked === undefined) return both([...(appendedOf.get(parent) ?? []), ...move]);
          children.delete(move);
          if (children.size === 0) made.delete(parent);
          return walked;
        },
        next,
        merge: "none",
      }))
        paths += 1;
      t.diagnostic(`${paths} paths`);
    });
}
