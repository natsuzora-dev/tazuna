import { expect } from "@playwright/test";
import { replay } from "../harness/replay.ts";
import { writeTrace } from "../harness/traces.ts";
import { screenAdapter } from "../support/screenAdapter.ts";
import { spec } from "../support/spec.ts";
import { test } from "./fixtures.ts";

for (const scenario of spec.scenarios.filter((s) => s.service === "screens"))
  test(scenario.name, async ({ page, held }) => {
    const screen = screenAdapter(page, held);
    writeTrace("screens", scenario.name, await replay(spec, scenario, screen));
    expect(screen.unboundCalls()).toEqual([]);
  });
