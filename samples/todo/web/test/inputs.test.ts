import { join } from "node:path";
import { drive, inputRuns, runFile } from "@natsuzora-dev/tazuna/verify";
import { test } from "vitest";
import { writeTrace } from "./harness/traces.ts";
import { serverAdapter } from "./support/serverAdapter.ts";
import { spec } from "./support/spec.ts";

/** The inputs that `tazuna generate spec inputs` wrote, which reach the parts of the spec that the scenarios leave out. */
const inputs = join(import.meta.dirname, "../../inputs");

for (const runner of ["todo", "notifier"] as const)
  test.for(inputRuns(spec, inputs).filter((r) => r.runner === runner))(
    `drive writes the trace of ${runner}'s run of the generated input $input`,
    async (run) => {
      writeTrace(runFile(run), await drive(spec, run, serverAdapter(runner)));
    },
  );
