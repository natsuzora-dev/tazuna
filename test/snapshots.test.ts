import assert from "node:assert/strict";
import { cpSync, type Dirent, existsSync, mkdirSync, mkdtempSync, readdirSync, rmSync, writeFileSync } from "node:fs";
import { join } from "node:path";
import { after, test } from "node:test";
import { testSpec } from "../src/cli/test.ts";
import { sameRef } from "../src/data/definitionRef.ts";
import { ownRun, snapshotPath } from "../src/data/traceFile.ts";
import type { ReportedViolation } from "../src/data/violation.ts";
import { checkedRoot } from "./examples.ts";

mkdirSync(join(import.meta.dirname, ".fixtures"), { recursive: true });
const copy = mkdtempSync(join(import.meta.dirname, ".fixtures", "snapshots-"));
after(() => rmSync(copy, { recursive: true, force: true }));
cpSync(join(import.meta.dirname, "service/Query/changed_answer_sent"), copy, { recursive: true });
writeFileSync(join(copy, "todo/__snapshots__/removed.jsonl"), "");
mkdirSync(join(copy, "todo/__snapshots__/notes"));

test("test writes no snapshot, and test --update rewrites snapshots without comparing, deletes snapshots without a scenario, and keeps and reports entries that are not snapshots", async () => {
  const spec = await checkedRoot(copy);
  const snapshots = join(spec.root, "todo/__snapshots__");
  const entries = readdirSync(snapshots, { withFileTypes: true });
  const isSnapshot = (e: Dirent) => e.isFile() && e.name.endsWith(".jsonl");
  const obsolete = entries
    .filter((e) => isSnapshot(e) && !spec.scenarios.some((s) => `${s.name}.jsonl` === e.name))
    .map((e) => e.name);
  const unknown = entries.filter((e) => !isSnapshot(e)).map((e) => `todo/__snapshots__/${e.name}`);
  assert.notDeepEqual(obsolete, []);
  assert.notDeepEqual(unknown, []);
  const unknownEntries = (violations: readonly ReportedViolation[]) => violations.map((p) => [p.kind, p.location.file]);
  const reported = unknown.map((path) => ["Uncomparable.unknownSnapshotEntry", path]);
  const [scenario] = spec.scenarios;
  assert.ok(scenario !== undefined);
  rmSync(snapshotPath(spec, ownRun(scenario)));
  const compared = testSpec(spec, { update: false, depth: 0, scenarios: spec.scenarios });
  assert.deepEqual(compared.written, []);
  assert.ok(
    compared.violations.some((p) => p.kind === "Uncomparable.missingSnapshot" && sameRef(p.scenario ?? null, scenario)),
  );
  assert.ok(!existsSync(snapshotPath(spec, ownRun(scenario))));
  const updated = testSpec(spec, { update: true, depth: 0, scenarios: spec.scenarios });
  assert.deepEqual(unknownEntries(updated.violations).toSorted(), reported.toSorted());
  assert.deepEqual(
    updated.removed.toSorted(),
    obsolete.map((f) => join(snapshots, f)),
  );
  assert.deepEqual(
    unknownEntries(testSpec(spec, { update: false, depth: 0, scenarios: spec.scenarios }).violations).toSorted(),
    reported.toSorted(),
  );
});
