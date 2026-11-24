import assert from "node:assert/strict";
import { chmodSync, copyFileSync, mkdirSync, mkdtempSync, rmSync, writeFileSync } from "node:fs";
import { join } from "node:path";
import { after, test } from "node:test";
import { fileURLToPath } from "node:url";
import { verifyTraces } from "../../src/cli/verify.ts";
import { InternalError } from "../../src/data/internalError.ts";
import { checkedRoot, fixture } from "../fixtures/fixtures.ts";

mkdirSync(join(import.meta.dirname, "../.fixtures"), { recursive: true });
const folder = mkdtempSync(join(import.meta.dirname, "../.fixtures", "verify-answers-"));
after(() => rmSync(folder, { recursive: true, force: true }));

// An engine that answers verify with no result for any trace and passes every other request to the real engine.
const engine = join(folder, "engine.mjs");
writeFileSync(
  engine,
  `#!/usr/bin/env node
import { spawnSync } from "node:child_process";
import { readFileSync } from "node:fs";
const input = readFileSync(0, "utf8");
if (input !== "" && JSON.parse(input).type === "verify") process.stdout.write('{"type":"verify","logs":[],"uncovered":[]}\\n');
else process.stdout.write(spawnSync(${JSON.stringify(fileURLToPath(import.meta.resolve("#engine")))}, { input, encoding: "utf8", maxBuffer: Infinity }).stdout);
`,
);
chmodSync(engine, 0o755);
process.env["TAZUNA_ENGINE"] = engine;

test("verify stops with an internal error, never a pass, when the engine gives no result for a trace", async () => {
  const shop = await checkedRoot(fixture("test", "noViolations", "command-output"));
  const traces = join(folder, "traces");
  mkdirSync(join(traces, "shop"), { recursive: true });
  copyFileSync(join(shop.root, "shop/__snapshots__/refundCreatedCharge.jsonl"), join(traces, "shop/trace.jsonl"));
  assert.throws(() => verifyTraces(shop, traces), InternalError);
});
