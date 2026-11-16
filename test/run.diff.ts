import assert from "node:assert/strict";
import { join, relative } from "node:path";
import { after, test } from "node:test";
import { haltingFaultKinds } from "../src/data/fault.generated.ts";
import type { Line, Scenario } from "../src/data/scenario.generated.ts";
import type { Step } from "../src/data/step.generated.ts";
import type { RejectionKind } from "../src/data/trace.generated.ts";
import { toJsonl } from "../src/data/trace.ts";
import { canonicalJson, type Json } from "../src/data/values.ts";
import type { Data, Violation } from "../src/data/violation.ts";
import { type Input, timed } from "../src/dsl/scenario.ts";
import { enabledMoves, orderedInputs, seenValues, valuesPerPayload } from "../src/explore/moves.ts";
import { enabledLines, orderedLines, seenLines, type Walked, walkAppended } from "../src/explore/paths.ts";
import { search } from "../src/explore/search.ts";
import type { Spec } from "../src/load/load.ts";
import type { LoadedScenario } from "../src/load/scenarios.ts";
import { definitionOfTraceName } from "../src/load/traceName.ts";
import { type Enabled, enabled } from "../src/observe/enabled.ts";
import { limits as tsLimits } from "../src/service/limits.ts";
import { byCallerKinds } from "../src/service/message.ts";
import { Halt } from "../src/service/state.ts";
import type { Participant } from "../src/sim/network.ts";
import { execute, extend, type Run, stepsOf } from "../src/sim/spec/execute.ts";
import { outcomeOf } from "../src/sim/spec/simulate.ts";
import { depth, loadRoot, runExamples } from "./examples.ts";
import { RunFunctions, SimFunctions } from "./lean/functions.ts";
import { invalidAfter, rejectedAnywhere } from "./lean/invalidMoves.ts";
import { Lean, type LeanRun } from "./lean/lean.ts";

const tazuna = join(import.meta.dirname, "..");

const lean = new Lean();
after(() => lean.close());

const roots = runExamples();

/** A path with its TS run, what TS found enabled after each input before the run halted, and its Lean run. */
interface Both {
  readonly path: readonly Input[];
  readonly ts: Run;
  readonly enabled: readonly Enabled[];
  readonly lean: LeanRun;
}

/**
 * Asserts that the TS and Lean runs of the same steps agree. Traces are compared as snapshot strings, character by
 * character.
 */
function compare(spec: Spec, service: string, both: Both): Both {
  const { ts: run, lean: fromLean } = both;
  const ts = run.outcome;
  const at = `steps ${JSON.stringify(stepsOf(spec, service, both.path))}`;
  assert.equal(toJsonl(fromLean.lines), toJsonl(ts.lines), `the traces differ for ${at}`);
  assert.deepEqual(
    fromLean.violations,
    ts.violations.map((v) => ({ kind: v.kind, definition: v.definition, data: v.data })),
    `the violations differ for ${at}`,
  );
  assert.deepEqual(fromLean.candidates, run.stepsFrom(0).candidates, `the candidates differ for ${at}`);
  assert.deepEqual(fromLean.enabled, both.enabled, `enabled differs for ${at}`);
  return both;
}

const functionsOf = (spec: Spec, service: string) => new RunFunctions(spec, service, (part) => lean.read(part));

/** Returns the TS run of the parent's path followed by `input`, continued from the parent's run. */
function extendTs(parent: Pick<Both, "ts" | "enabled">, input: Input): Pick<Both, "ts" | "enabled"> {
  const ts = extend(parent.ts, input);
  return { ts, enabled: ts.enabled === undefined ? parent.enabled : [...parent.enabled, ts.enabled] };
}

/** Returns both runs of a path from the start. TS runs it one input at a time to find what is enabled after each. */
function runBoth(spec: Spec, service: string, path: readonly Input[]): Both {
  return compare(spec, service, {
    path,
    ...path.reduce(extendTs, { ts: execute(spec, service, []), enabled: [] }),
    lean: lean.run(spec, service, stepsOf(spec, service, path), functionsOf(spec, service)),
  });
}

/** Returns both runs of the parent's path followed by `input`, each continued from the parent's run. */
function stepBoth(spec: Spec, service: string, parent: Both, input: Input): Both {
  const [step] = stepsOf(spec, service, [input]) as [Step];
  return compare(spec, service, {
    path: [...parent.path, input],
    ...extendTs(parent, input),
    lean: lean.extend(parent.lean.handle, step, functionsOf(spec, service)),
  });
}

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

for (const { name, spec } of specs) {
  const seen = seenValues(spec);
  for (const scenario of spec.legacyScenarios)
    test(`${name}: ${scenario.service}/${scenario.name} and every path that appends up to ${depth} inputs to it give the same result in TS and Lean`, (t) => {
      const service = scenario.service;
      const start = timed(scenario.definition);
      const first = runBoth(spec, service, start);
      const anywhere = rejectedAnywhere(spec, service, first.ts.now.toString());
      const enabledAfter = enabledMoves(spec, service, seen, valuesPerPayload);
      // Invalid inputs are placed only at the end of a path.
      const invalid = new WeakSet<Input>();
      // Per parent, the runs that next made for each enabled input with every order of the deadlines in its ties, until
      // the search takes them; the invalid inputs are run when taken. A parent's inputs can be the same objects as
      // another parent's.
      const made = new Map<Both, Map<Input, Both>>();
      const next = (path: readonly Input[], parent: Both): Input[] => {
        const { ts: run } = parent;
        const last = path.at(-1);
        if (run.halted !== undefined || (last !== undefined && invalid.has(last))) return [];
        const children = new Map(
          enabledAfter(run).flatMap((input) =>
            orderedInputs(
              input,
              (i) => stepBoth(spec, service, parent, i),
              (both) => both.ts.unchosenDeadlines,
            ).map((c) => [c.input, c.result] as const),
          ),
        );
        made.set(parent, children);
        const enabled = [...children.keys()];
        const others = [...invalidAfter(spec, service, run, enabled), ...(path === start ? anywhere : [])];
        for (const input of others) invalid.add(input);
        return [...enabled, ...others];
      };
      let paths = 0;
      // Every path of up to `depth` appended inputs, in every order. Merging paths by state would compare the TS
      // fingerprint, which assumes the TS runtime that this test checks.
      for (const _ of search<Input, Both>({
        start: { path: start, result: first },
        bound: depth,
        step: (parent, input) => {
          const children = made.get(parent);
          const both = children?.get(input);
          if (children === undefined || both === undefined) return stepBoth(spec, service, parent, input);
          children.delete(input);
          if (children.size === 0) made.delete(parent);
          return both;
        },
        next,
        merge: "none",
      }))
        paths += 1;
      t.diagnostic(`${paths} paths`);
    });
}

/** What a walk shows, as Lean's reply to `simulate` with `walk` gives it. */
function walkedOutcome(walked: Walked) {
  const { world } = walked;
  return {
    ...outcomeOf(world),
    participants: outcomeOf(world).participants.map((p) => {
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
function invalidLines(spec: Spec, sc: Scenario, walked: Walked, enabledLines: readonly Line[]): Line[] {
  const malformed = { value: "not an object", holes: [] };
  const command = spec.structure.definitions.find((d) => d.kind === "command" && d.service === sc.service);
  const answer = enabledLines.find((l) => l.type === "answer");
  const operate = enabledLines.find((l) => l.type === "operate");
  return [
    { type: "at", time: walked.world.now.subtract({ milliseconds: 1 }).toString(), order: [] },
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
      const invalid = new WeakSet<Line>();
      const made = new Map<Walked, Map<Line, Walked>>();
      const next = (path: readonly Line[], walked: Walked): Line[] => {
        const last = path.at(-1);
        const stopped =
          walked.world.halted !== undefined || [...walked.world.participants.values()].some((p) => p.halted);
        if (stopped || (last !== undefined && invalid.has(last))) return [];
        const appended = appendedOf.get(walked) ?? [];
        let lines: Line[];
        try {
          lines = enabledAfter(path, walked);
        } catch (error) {
          if (error instanceof Halt) return [];
          throw error;
        }
        const children = new Map(
          lines.flatMap((line) => orderedLines(line, (l) => both([...appended, l])).map((c) => [c.line, c.walked])),
        );
        made.set(walked, children);
        const others = invalidLines(spec, sc, walked, lines);
        for (const line of others) invalid.add(line);
        return [...children.keys(), ...others];
      };
      let paths = 0;
      for (const _ of search<Line, Walked>({
        start: { path: sc.lines, result: both([]) },
        bound: depth,
        step: (parent, line) => {
          const children = made.get(parent);
          const walked = children?.get(line);
          if (children === undefined || walked === undefined) return both([...(appendedOf.get(parent) ?? []), line]);
          children.delete(line);
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

test("A step that names a command, query, subscription, or screen of another service, or that receives an event outside the contract, stops without writing a line in both TS and Lean", () => {
  const spec = (item: string) => {
    const found = specs.find((s) => s.name === join("test/service", item));
    assert.ok(found);
    return found.spec;
  };
  const named = (found: Spec, service: string, kind: "command" | "query" | "event" | "screen", name: string) => {
    const d = definitionOfTraceName(found, service, name, kind);
    assert.ok(d !== undefined);
    return d as never;
  };
  const shop = spec("Command/command-output");
  const screens = spec("Chart/Request/child-screen");
  const time = "2026-10-25T10:00:00+09:00";
  const cases: readonly [Spec, string, Input, Data][] = [
    [
      shop,
      "shop",
      { type: "command", command: named(shop, "shop", "command", "payments.createCharge"), input: { amount: 1 }, time },
      { kind: "InvalidInput.unownedTarget", target: { service: "payments", name: "createCharge" } },
    ],
    [
      screens,
      "screens",
      { type: "query", query: named(screens, "screens", "query", "todo.tasks"), input: {}, time },
      { kind: "InvalidInput.unownedTarget", target: { service: "todo", name: "tasks" } },
    ],
    [
      screens,
      "screens",
      { type: "subscribe", query: named(screens, "screens", "query", "todo.tasks"), input: {}, time },
      { kind: "InvalidInput.unownedTarget", target: { service: "todo", name: "tasks" } },
    ],
    [
      shop,
      "shop",
      { type: "event", event: named(shop, "shop", "event", "orderPlaced"), payload: { amount: 1 }, time },
      { kind: "InvalidInput.unlistedEvent", event: { service: "shop", name: "orderPlaced" } },
    ],
    ...(["operation", "unacceptedOperation"] as const).map((type): [Spec, string, Input, Data] => [
      screens,
      "todo",
      { type, screen: named(screens, "todo", "screen", "screens.homeScreen"), control: "openList", payload: {}, time },
      { kind: "InvalidInput.unownedTarget", target: { service: "screens", name: "homeScreen" } },
    ]),
  ];
  for (const [found, service, input, expected] of cases) {
    const ts = runBoth(found, service, [input]).ts.outcome;
    assert.deepEqual(
      ts.violations.map((v) => ({ kind: v.kind, ...v.data })),
      [expected],
    );
    assert.deepEqual(
      ts.lines.filter((l) => l.dir === "in"),
      [],
    );
  }
});
