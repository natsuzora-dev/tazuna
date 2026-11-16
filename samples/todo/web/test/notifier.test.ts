import { drive, peerSnapshots } from "@natsuzora-dev/tazuna/verify";
import { test } from "vitest";
import { writeTrace } from "./harness/traces.ts";
import { serverAdapter } from "./support/serverAdapter.ts";
import { spec } from "./support/spec.ts";

test.for(spec.scenarios.filter((s) => s.service === "notifier"))(
  "drive writes the trace of notifier's scenario $name",
  async (scenario) => {
    writeTrace("notifier", scenario.name, await drive(spec, scenario, serverAdapter("notifier")));
  },
);

test.for(peerSnapshots(spec).filter((s) => s.runner === "notifier"))(
  "drive writes the trace of notifier's run $name of a $service scenario",
  async (snapshot) => {
    writeTrace(snapshot.service, snapshot.name, await drive(spec, snapshot, serverAdapter("notifier")));
  },
);
