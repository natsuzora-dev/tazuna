import assert from "node:assert/strict";
import { cpSync, type Dirent, existsSync, mkdirSync, mkdtempSync, readdirSync, rmSync } from "node:fs";
import { join } from "node:path";
import { after, test } from "node:test";
import { testSpec } from "../src/cli/test.ts";
import { sameRef } from "../src/data/definitionRef.ts";
import type { Problem } from "../src/data/problem.ts";
import { snapshotPath } from "../src/data/traceFile.ts";
import { loadSpec } from "../src/load/load.ts";

mkdirSync(join(import.meta.dirname, ".fixtures"), { recursive: true });
const copy = mkdtempSync(join(import.meta.dirname, ".fixtures", "snapshots-"));
after(() => rmSync(copy, { recursive: true, force: true }));
cpSync(join(import.meta.dirname, "verify/uncomparable/snapshot/unpaired"), copy, { recursive: true });

test("test writes no snapshot, and test --update rewrites snapshots without comparing, deletes snapshots without a scenario, and keeps and reports entries that are not snapshots", async () => {
  const spec = await loadSpec(copy);
  const snapshots = join(spec.root, "todo/__snapshots__");
  const entries = readdirSync(snapshots, { withFileTypes: true });
  const isSnapshot = (e: Dirent) => e.isFile() && e.name.endsWith(".jsonl");
  const obsolete = entries
    .filter((e) => isSnapshot(e) && !spec.scenarios.some((s) => `${s.name}.jsonl` === e.name))
    .map((e) => e.name);
  const unknown = entries.filter((e) => !isSnapshot(e)).map((e) => `todo/__snapshots__/${e.name}`);
  assert.notDeepEqual(obsolete, []);
  assert.notDeepEqual(unknown, []);
  const unknownEntries = (problems: readonly Problem[]) => problems.map((p) => [p.kind, p.location.file]);
  const reported = unknown.map((path) => ["Uncomparable.unknownSnapshotEntry", path]);
  const [scenario] = spec.scenarios;
  assert.ok(scenario !== undefined);
  rmSync(snapshotPath(spec, scenario));
  const compared = testSpec(spec, { update: false, depth: 0 });
  assert.deepEqual(compared.written, []);
  assert.ok(
    compared.problems.some((p) => p.kind === "Uncomparable.missingSnapshot" && sameRef(p.scenario ?? null, scenario)),
  );
  assert.ok(!existsSync(snapshotPath(spec, scenario)));
  const updated = testSpec(spec, { update: true, depth: 0 });
  assert.deepEqual(unknownEntries(updated.problems).toSorted(), reported.toSorted());
  assert.deepEqual(
    updated.removed.toSorted(),
    obsolete.map((f) => join(snapshots, f)),
  );
  assert.deepEqual(
    unknownEntries(testSpec(spec, { update: false, depth: 0 }).problems).toSorted(),
    reported.toSorted(),
  );
});
