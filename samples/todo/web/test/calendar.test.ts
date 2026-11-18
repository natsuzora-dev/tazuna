import type { TraceLine } from "@natsuzora-dev/tazuna";
import { lineIds } from "@natsuzora-dev/tazuna/verify";
import { test } from "vitest";
import { nextBusinessDay } from "../src/calendar/calendar.server.ts";
import { writeTrace } from "./harness/traces.ts";
import { toSpec } from "./support/answers.ts";

const inputs = { friday: "2026-10-30", saturday: "2026-10-31", sunday: "2026-11-01", monday: "2026-11-02" };

test("nextBusinessDay writes the trace of the calendar double's answers", async () => {
  const time = Temporal.Now.instant().toString();
  const trace: TraceLine[] = [];
  const lineId = lineIds();
  for (const [id, day] of Object.entries(inputs)) {
    const from = Temporal.PlainDate.from(day);
    const result = await nextBusinessDay({ from });
    trace.push({ time, dir: "in", type: "query", id, name: "nextBusinessDay", input: { from } });
    trace.push({ time, dir: "out", type: "answer", id: lineId("answer"), to: id, answer: toSpec.calendar(result) });
  }
  writeTrace("calendar/nextBusinessDay.jsonl", trace);
});
