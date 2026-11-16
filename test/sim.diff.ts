import assert from "node:assert/strict";
import { readFileSync } from "node:fs";
import { join, relative } from "node:path";
import { after, test } from "node:test";
import { scenario } from "../src/data/scenario.generated.ts";
import { canonicalJson, type Json } from "../src/data/values.ts";
import type { Violation } from "../src/data/violation.ts";
import { timed } from "../src/dsl/scenario.ts";
import { loadSpec } from "../src/load/load.ts";
import { type NamedForm, peerArrivals } from "../src/sim/peer.ts";
import { peerFindings, peerRunFindings } from "../src/sim/peerCheck.ts";
import { execute } from "../src/sim/spec/execute.ts";
import { peerDerivations, runPeer } from "../src/sim/spec/peers.ts";
import { outcomeOf, simulateSpec } from "../src/sim/spec/simulate.ts";
import { outcomeSuffix, runExamples, scenarioSuffix, simExamples } from "./examples.ts";
import { SimFunctions, tagged } from "./lean/functions.ts";
import { Lean } from "./lean/lean.ts";

const lean = new Lean();
after(() => lean.close());

const roots = [join(import.meta.dirname, "../samples/todo/spec"), ...runExamples()];

/** The violation as Lean's Violation holds it: its kind, definition and data. */
const violationValue = ({ kind, definition, data }: Violation) => ({ kind, definition, data });

const same = (a: unknown, b: unknown) => canonicalJson(a as Json) === canonicalJson(b as Json);

test("Lean and TS derive the same inputs of each peer from each scenario run that did not halt, and find the same violations of the scenario's mocks in the peer's run", async () => {
  let checked = 0;
  for (const root of roots) {
    const spec = await loadSpec(root);
    for (const scenario of spec.legacyScenarios) {
      const run = execute(spec, scenario.service, timed(scenario.definition));
      if (run.halted !== undefined) continue;
      for (const d of peerDerivations(spec, scenario, run)) {
        const at = `${relative(join(import.meta.dirname, ".."), root)} ${scenario.service}.${scenario.name} ${d.peer}`;
        const lines = run.outcome.lines;
        const { derived, run: peerRun, halted, reported } = runPeer(spec, scenario.service, lines, d);
        const recording = (form: NamedForm) => {
          const forms: [string, unknown, unknown][] = [];
          const recorded = (name: string, value: unknown) => {
            const v = form(name, value);
            forms.push([name, value, tagged(v)]);
            return v;
          };
          return [forms, recorded] as const;
        };
        const [peerForms, peerForm] = recording(d.peerForm);
        const [ownInputForms, ownInputForm] = recording(d.ownInputForm);
        const findings = peerFindings(
          scenario.service,
          { ...d, peerForm, ownInputForm },
          peerArrivals(scenario.service, d, lines),
          lines,
          peerRun.outcome.lines,
          halted,
        );
        const fromLean = lean.peer({
          service: scenario.service,
          peer: d.peer,
          received: d.received,
          fromLines: d.fromLines,
          state: d.state,
          elsewhere: d.elsewhere,
          lines,
          peerLines: peerRun.outcome.lines,
          halted: halted ?? null,
          peerForms,
          ownInputForms,
          reported: reported.map(({ origin, violation }) => [origin, violationValue(violation)] as const),
        });
        assert.ok(same(fromLean.inputs, derived), `the derived inputs differ for ${at}`);
        assert.ok(same(fromLean.findings, findings), `the findings differ for ${at}`);
        assert.ok(
          same(
            fromLean.runFindings,
            peerRunFindings(reported).map(({ origin, violation }) => ({
              origin,
              violation: violationValue(violation),
            })),
          ),
          `the findings of the peer's run differ for ${at}`,
        );
        checked += 1;
      }
    }
  }
  assert.ok(checked > 0);
});

for (const { root, scenarios } of simExamples()) {
  const spec = await loadSpec(root);
  for (const name of scenarios)
    test(`${relative(join(import.meta.dirname, ".."), root)}/${name}: Lean and TS simulate the scenario alike, and the outcome is ${name}${outcomeSuffix}`, () => {
      const sc = scenario.parse(JSON.parse(readFileSync(join(root, `${name}${scenarioSuffix}`), "utf8")));
      const ts = outcomeOf(simulateSpec(spec, sc));
      const fromLean = lean.simulate(spec, sc, new SimFunctions(spec, (part) => lean.read(part)));
      assert.equal(canonicalJson(fromLean as Json), canonicalJson(ts as unknown as Json));
      assert.equal(
        canonicalJson(ts as unknown as Json),
        canonicalJson(JSON.parse(readFileSync(join(root, `${name}${outcomeSuffix}`), "utf8")) as Json),
      );
    });
}

for (const root of roots) {
  const spec = await loadSpec(root);
  for (const { service, name, definition } of spec.scenarios)
    test(`${relative(join(import.meta.dirname, ".."), root)}: Lean and TS simulate ${service}/${name} alike`, () => {
      const ts = outcomeOf(simulateSpec(spec, definition.scenario));
      const fromLean = lean.simulate(spec, definition.scenario, new SimFunctions(spec, (part) => lean.read(part)));
      assert.equal(canonicalJson(fromLean as Json), canonicalJson(ts as unknown as Json));
    });
}
