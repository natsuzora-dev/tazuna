import { drive, peerSnapshots } from "@natsuzora-dev/tazuna/verify";
import { expect } from "@playwright/test";
import { writeTrace } from "../harness/traces.ts";
import { screenAdapter } from "../support/screenAdapter.ts";
import { spec } from "../support/spec.ts";
import { test } from "./fixtures.ts";

for (const scenario of spec.scenarios.filter((s) => s.service === "screens"))
  test(scenario.name, async ({ page, held }) => {
    const screen = screenAdapter(page, held);
    writeTrace("screens", scenario.name, await drive(spec, scenario, screen));
    expect(screen.unboundCalls()).toEqual([]);
  });

for (const snapshot of peerSnapshots(spec).filter((s) => s.runner === "screens"))
  test(`${snapshot.name} of a ${snapshot.service} scenario`, async ({ page, held }) => {
    const screen = screenAdapter(page, held);
    writeTrace(snapshot.service, snapshot.name, await drive(spec, snapshot, screen));
    expect(screen.unboundCalls()).toEqual([]);
  });
