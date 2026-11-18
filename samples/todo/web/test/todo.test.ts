import { drive, runFile, snapshotRuns } from "@natsuzora-dev/tazuna/verify";
import { test } from "vitest";
import { writeTrace } from "./harness/traces.ts";
import { serverAdapter } from "./support/serverAdapter.ts";
import { spec } from "./support/spec.ts";

test.for(snapshotRuns(spec).filter((r) => r.runner === "todo"))(
  "drive writes the trace of todo's run of the $service scenario $scenario",
  async (run) => {
    writeTrace(runFile(run), await drive(spec, run, serverAdapter("todo")));
  },
);
