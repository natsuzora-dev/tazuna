import assert from "node:assert/strict";
import { relative } from "node:path";
import { test } from "node:test";
import { type Input, timed } from "../src/dsl/scenario.ts";
import { enabledMoves, orderedInputs, seenValues, valuesPerPayload } from "../src/explore/moves.ts";
import { search } from "../src/explore/search.ts";
import { execute, extend, type Run } from "../src/sim/spec/execute.ts";
import { depth, loadRoot, maskedStack, runExamples } from "./examples.ts";

const observed = (run: Run) => ({
  outcome: { ...run.outcome, violations: run.outcome.violations.map(maskedStack) },
  halted: run.halted && maskedStack(run.halted),
  enabled: run.enabled,
  answered: run.answered.map((p) => p?.id),
  inputLines: run.inputLines,
  fingerprint: run.fingerprint(),
});

for (const root of runExamples()) {
  const spec = await loadRoot(root);
  test(`${relative(import.meta.dirname, root)}: on each path that appends up to ${depth} inputs to a scenario, continuing from the parent's run gives the same result as running from the start, also for inputs that choose the order of deadlines due at one time and for inputs appended to a halted path`, () => {
    const seen = seenValues(spec);
    for (const scenario of spec.legacyScenarios) {
      const service = scenario.service;
      const next = enabledMoves(spec, service, seen, valuesPerPayload);
      const same = (parent: Run, path: readonly Input[]) =>
        assert.deepEqual(observed(extend(parent, path.at(-1) as Input)), observed(execute(spec, service, path)));
      const inputs = timed(scenario.definition);
      const base = execute(spec, service, inputs);
      for (const { path, result, parent } of search({
        start: { path: inputs, result: base },
        bound: depth,
        step: extend,
        next: (_, run) =>
          run.halted === undefined
            ? next(run).flatMap((input) =>
                orderedInputs(
                  input,
                  (i) => extend(run, i),
                  (r) => r.unchosenDeadlines,
                ).map((c) => c.input),
              )
            : [],
        merge: "none",
      })) {
        if (parent === undefined) continue;
        same(parent, path);
        if (result.halted !== undefined) same(result, [...path, path.at(-1) as Input]);
      }
    }
  });
}
