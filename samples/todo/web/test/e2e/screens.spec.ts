import { join } from "node:path";
import { drive, inputRuns, runFile, snapshotRuns } from "@natsuzora-dev/tazuna/verify";
import { expect } from "@playwright/test";
import { writeTrace } from "../harness/traces.ts";
import { screenAdapter } from "../support/screenAdapter.ts";
import { spec } from "../support/spec.ts";
import { test } from "./fixtures.ts";

for (const run of snapshotRuns(spec).filter((r) => r.runner === "screens"))
  test(`${run.scenario} of ${run.service}`, async ({ page, held }) => {
    const screen = screenAdapter(page, held);
    writeTrace(runFile(run), await drive(spec, run, screen));
    expect(screen.unboundCalls()).toEqual([]);
  });

/** The inputs that `tazuna generate spec inputs` wrote for the screens, beside the scenarios. */
const inputs = join(import.meta.dirname, "../../../inputs");

for (const run of inputRuns(spec, inputs).filter((r) => r.runner === "screens"))
  test(`the generated input ${run.input}`, async ({ page, held }) => {
    const screen = screenAdapter(page, held);
    writeTrace(runFile(run), await drive(spec, run, screen));
    expect(screen.unboundCalls()).toEqual([]);
  });
