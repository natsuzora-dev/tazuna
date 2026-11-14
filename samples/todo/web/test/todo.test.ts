import { peerSnapshots } from "@natsuzora-dev/tazuna/verify";
import { test } from "vitest";
import { replay } from "./harness/replay.ts";
import { writeTrace } from "./harness/traces.ts";
import { serverAdapter } from "./support/serverAdapter.ts";
import { spec } from "./support/spec.ts";

test.for(spec.scenarios.filter((s) => s.service === "todo"))(
  "replay writes the trace of todo's scenario $name",
  async (scenario) => {
    writeTrace("todo", scenario.name, await replay(spec, scenario, serverAdapter("todo")));
  },
);

test.for(peerSnapshots(spec).filter((s) => s.runner === "todo"))(
  "replay writes the trace of todo's run $name of a $service scenario",
  async (snapshot) => {
    writeTrace(snapshot.service, snapshot.name, await replay(spec, snapshot, serverAdapter("todo")));
  },
);
