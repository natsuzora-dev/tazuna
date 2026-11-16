import assert from "node:assert/strict";
import { join, relative } from "node:path";
import { after, test } from "node:test";
import { canonicalJson, type Json } from "../src/data/values.ts";
import { timed } from "../src/dsl/scenario.ts";
import { loadSpec } from "../src/load/load.ts";
import { execute } from "../src/run/execute.ts";
import { ownInputForm, peerDerivations, peerForm, runPeer } from "../src/run/peers.ts";
import { type NamedForm, peerArrivals, peerFindings } from "../src/semantics/system/peer.ts";
import { runExamples } from "./examples.ts";
import { tagged } from "./lean/functions.ts";
import { Lean } from "./lean/lean.ts";

const lean = new Lean();
after(() => lean.close());

const roots = [join(import.meta.dirname, "../samples/todo/spec"), ...runExamples()];

const same = (a: unknown, b: unknown) => canonicalJson(a as Json) === canonicalJson(b as Json);

test("Lean and TS derive the same inputs of each peer from each scenario run that did not halt, and find the same violations of the scenario's mocks in the peer's run", async () => {
  let checked = 0;
  for (const root of roots) {
    const spec = await loadSpec(root);
    for (const scenario of spec.scenarios) {
      const run = execute(spec, scenario.service, timed(scenario.definition));
      if (run.halted !== undefined) continue;
      for (const d of peerDerivations(spec, scenario, run)) {
        const at = `${relative(join(import.meta.dirname, ".."), root)} ${scenario.service}.${scenario.name} ${d.peer}`;
        const lines = run.outcome.lines;
        const forms = peerForm(spec, d.peer);
        const own = ownInputForm(spec, scenario.service);
        const { derived, run: peerRun, halted } = runPeer(spec, forms, own, scenario.service, lines, d);
        const recording = (form: NamedForm) => {
          const forms: [string, unknown, unknown][] = [];
          const recorded = (name: string, value: unknown) => {
            const v = form(name, value);
            forms.push([name, value, tagged(v)]);
            return v;
          };
          return [forms, recorded] as const;
        };
        const [peerForms, recorded] = recording(forms);
        const [ownInputForms, recordedInput] = recording(own);
        const arrivals = peerArrivals(scenario.service, d.peer, d.received, d.fromLines, d.state, d.elsewhere, lines);
        const findings = peerFindings(
          recorded,
          recordedInput,
          scenario.service,
          d.peer,
          d.fromLines,
          arrivals,
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
        });
        assert.ok(same(fromLean.inputs, derived), `the derived inputs differ for ${at}`);
        assert.ok(same(fromLean.findings, findings), `the findings differ for ${at}`);
        checked += 1;
      }
    }
  }
  assert.ok(checked > 0);
});
