import assert from "node:assert/strict";
import { join } from "node:path";
import { describe, test } from "node:test";
import type { Step } from "../src/data/step.generated.ts";
import type { Uncovered } from "../src/data/uncovered.ts";
import { timed } from "../src/dsl/scenario.ts";
import { type Bounds, explore } from "../src/explore/index.ts";
import { seenValues } from "../src/explore/moves.ts";
import { loadSpec, type Spec } from "../src/load/load.ts";
import { execute, stepsOf } from "../src/sim/spec/execute.ts";
import { depth, groupExamples } from "./examples.ts";
import { testEveryKind, testExamples } from "./expected.ts";

const examples = join(import.meta.dirname, "run/choiceDependent/Observe/ChoiceDependent");
const separateRegions = await loadSpec(join(examples, "answer-order"));
const deadlines = await loadSpec(join(examples, "deadline-order"));

function explored(spec: Spec, name: string, bounds: Bounds) {
  const s = spec.legacyScenarios.find((scenario) => scenario.name === name);
  assert.ok(s !== undefined);
  const inputs = timed(s.definition);
  const { found, paths } = explore(spec, s, inputs, execute(spec, s.service, inputs), {
    seen: seenValues(spec),
    concurrent: new Map(),
    bounds,
  });
  return { found, paths: paths.map((p) => stepsOf(spec, s.service, p.appendedInputs)) };
}

const answerTo = (step: Step | undefined) => (step?.type === "answer" ? step.target : undefined);

describe("explore", () => {
  test("explore reports no pair of answers whose two orders give the same result and does not extend a path that reaches the state of an earlier path", () => {
    const { found, paths } = explored(separateRegions, "saveOnly", { depth: 3, valuesPerPayload: 2 });
    assert.deepEqual(found, []);
    const continued = (first: string, second: string) =>
      paths.filter((p) => p.length === 3 && answerTo(p[0]) === first && answerTo(p[1]) === second);
    assert.ok(continued("todo.saveTask", "notes.saveNote").length > 0);
    assert.deepEqual(continued("notes.saveNote", "todo.saveTask"), []);
  });

  test("explore keeps within the bounds on the number of appended inputs and on the number of values it tries for payloads and answers", () => {
    const { paths } = explored(separateRegions, "saveOnly", { depth: 2, valuesPerPayload: 3 });
    assert.ok(paths.some((p) => p.length === 2));
    assert.ok(paths.every((p) => p.length <= 2));
    const renames = new Set(
      explored(separateRegions, "saveOnly", { depth: 1, valuesPerPayload: 3 }).paths.flatMap((p) =>
        p.flatMap((s) => (s.type === "operation" && s.control === "rename" ? [JSON.stringify(s.payload)] : [])),
      ),
    );
    assert.equal(renames.size, 3);
    const answers = new Set(
      explored(separateRegions, "saveOnly", { depth: 1, valuesPerPayload: 2 }).paths.flatMap((p) =>
        p.flatMap((s) => (s.type === "answer" && s.target === "todo.saveTask" ? [JSON.stringify(s.answer)] : [])),
      ),
    );
    assert.deepEqual(
      [...answers],
      ['{"result":"accepted"}', '{"result":"rejected","rejection":{"kind":"unavailable"}}'],
    );
  });

  test("explore advances the time to just before the next deadline", () => {
    const { paths } = explored(deadlines, "addOnly", { depth: 1, valuesPerPayload: 2 });
    assert.ok(paths.some((p) => p[0]?.type === "time" && p[0].time === "2026-10-25T01:59:59.999Z"));
  });
});

describe("Uncovered examples", () => {
  const uncoveredExamples = groupExamples("explore", "uncovered");

  testExamples(uncoveredExamples, "Uncovered", ["test", ".", "--depth", String(depth), "--coverage"]);

  const kinds: Readonly<Record<Uncovered["kind"], true>> = {
    "Uncovered.request": true,
    "Uncovered.successAnswer": true,
    "Uncovered.bindsRejection": true,
    "Uncovered.requiresRejection": true,
    "Uncovered.automation": true,
    "Uncovered.automationBindingValue": true,
    "Uncovered.automationBindingNull": true,
    "Uncovered.automationGuard": true,
    "Uncovered.transition": true,
    "Uncovered.guardFalse": true,
    "Uncovered.state": true,
  };

  testEveryKind(uncoveredExamples, Object.keys(kinds));
});
