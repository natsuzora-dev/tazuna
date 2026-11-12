import { test } from "vitest";
import { replay } from "./harness/replay.ts";
import { writeTrace } from "./harness/traces.ts";
import { serverAdapter } from "./support/serverAdapter.ts";
import { spec } from "./support/spec.ts";

test.for(spec.scenarios.filter((s) => s.service === "notifier"))(
  "replay writes the trace of notifier's scenario $name",
  async (scenario) => {
    writeTrace("notifier", scenario.name, await replay(spec, scenario, serverAdapter("notifier")));
  },
);
